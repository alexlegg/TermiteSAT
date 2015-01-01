{-# LANGUAGE RecordWildCards, ViewPatterns, NamedFieldPuns #-}
module Expression.Expression (
      ExpressionT(..)
    , ExprVar(..)
    , Expression
    , Section(..)
    , Sign(..)
    , Var(..)
    , Assignment(..)

    , exprIndex
    , flipSign
    , emptyManager
    , getChildren
    , lookupExpression
    , lookupVar
    , traverseExpression
    , foldlExpression
    , foldrExpression
    , unrollExpression
    , setRank
    , setHatVar
    , conjunct
    , disjunct
    , equate
    , implicate
    , negation
    , equalsConstant
    , trueExpr
    , falseExpr
    , literal
    , toDimacs
    , makeCopy
    , pushCache
    , popCache
    , printExpression
    , makeAssignment
    , assignmentToExpression
    , blockAssignment
    , setVarRank
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.ST.Safe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Bits (testBit)
import Data.Foldable (foldlM)
import Data.Maybe
import Utils.Utils
import Debug.Trace

type ExpressionT m = StateT ExprManager (EitherT String m)

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . left

data ExprVar = ExprVar {
    varname     :: String,
    varsect     :: Section,
    bit         :: Int,
    rank        :: Int
    } deriving (Eq, Ord)

instance Show ExprVar where
    show v = let ExprVar{..} = v in varname ++ show rank ++ "[" ++ show bit ++ "]"

data Var = Var Sign Int deriving (Show, Eq, Ord)

var (Var _ v)   = v
sign (Var s _)  = s
lit (Var Pos v) = v
lit (Var Neg v) = -v

data Sign = Pos | Neg deriving (Show, Eq, Ord)

flipSign Pos = Neg
flipSign Neg = Pos

flipAssignment (Assignment s v) = Assignment (flipSign s) v

data Expr   = ETrue
            | EFalse
            | ELit ExprVar
            | ENot Var
            | ECopy Int [ExprVar] Var
            | EEquals Var Var
            | EConjunct [Var]
            | EDisjunct [Var]
            deriving (Eq, Ord, Show)

data Expression = Expression {
      eindex    :: Int
    , expr      :: Expr
    } deriving (Eq, Ord, Show)

exprIndex :: Expression -> Int
exprIndex = eindex

children :: Expr -> [Var]
children (ETrue)            = []
children (EFalse)           = []
children (ELit _)           = []
children (ENot v)           = [v]
children (ECopy c _ v)      = [v]
children (EEquals x y)      = [x, y]
children (EConjunct vs)     = vs
children (EDisjunct vs)     = vs

setChildren :: Expr -> [Var] -> Expr
setChildren (ETrue) _           = ETrue
setChildren (EFalse) _          = EFalse
setChildren (ELit l) _          = ELit l
setChildren (ENot _) vs         = ENot (head vs)
setChildren (ECopy c d _) vs    = ECopy c d (head vs)
setChildren (EEquals _ _) vs    = let (x:y:[]) = vs in EEquals x y
setChildren (EConjunct _) vs    = EConjunct vs
setChildren (EDisjunct _) vs    = EDisjunct vs

type CopyId = Int
type ExprId = Int

data ExprManager = ExprManager {
      maxIndex      :: ExprId
    , exprMap       :: Map.Map ExprId Expr
    , depMap        :: Map.Map ExprId (Set.Set ExprId)
    , copies        :: [ExprId]
    , indexMap      :: Map.Map Expr ExprId
    , dCache        :: DimacsCache
} deriving (Eq)

data DimacsCache = DimacsCache {
      dMap          :: Map.Map (CopyId, ExprId) (Int, [[Int]])
    , dMax          :: Int
    , childCache    :: Maybe DimacsCache
} deriving (Eq)

instance Show ExprManager where
    show m = let ExprManager{..} = m in
        "maxIndex: " ++ show maxIndex ++
        Map.foldl (\a b -> a ++ "\n" ++ show b) "" exprMap

data Section = StateVar | ContVar | UContVar | HatVar
    deriving (Show, Eq, Ord)

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

emptyManager = ExprManager { 
                  maxIndex      = 1
                , exprMap       = Map.empty
                , depMap        = Map.empty
                , copies        = []
                , indexMap      = Map.empty
                , dCache        = emptyCache 1
                }

emptyCache di = DimacsCache {
                  dMap          = Map.empty
                , dMax          = di
                , childCache    = Nothing
                }

pushCache :: Monad m => ExpressionT m ()
pushCache = do
    m <- get
    put m { dCache = add (dCache m) }
    where
        add dc@(childCache -> Just c)   = dc { childCache = Just (add c) }
        add dc@(childCache -> Nothing)  = dc { childCache = Just (emptyCache (dMax dc)) }

popCache :: Monad m => ExpressionT m ()
popCache = do
    m <- get
    put m { dCache = fromJust (rem (dCache m)) }
    where
        rem dc@(childCache -> Just c)   = Just (dc { childCache = rem c })
        rem dc@(childCache -> Nothing)  = Nothing

addExpression :: Monad m => Expr -> ExpressionT m Expression
addExpression e = do
    m@ExprManager{..} <- get
    case Map.lookup e indexMap of
        Nothing -> do
            let i = maxIndex
            deps <- childDependencies e
            put m {
                maxIndex    = maxIndex+1,
                exprMap     = Map.insert i e exprMap,
                depMap      = Map.insert i (Set.insert i deps) depMap,
                indexMap    = Map.insert e i indexMap}
            return $ Expression { eindex = i, expr = e }
        Just i -> do
            return $ Expression { eindex = i, expr = e }

childDependencies e = do
    m@ExprManager{..} <- get
    let cs = filter (\x -> not (var x `elem` copies)) (children e)
    let deps = map (\x -> Map.lookup (var x) depMap) cs
    return $ Set.unions (Set.fromList (map var (children e)) : catMaybes deps)


lookupExpression :: Monad m => Int -> ExpressionT m (Maybe Expression)
lookupExpression i = do
    ExprManager{..} <- get
    case Map.lookup i exprMap of
        Nothing     -> return Nothing
        (Just exp)  -> return $ Just (Expression { eindex = i, expr = exp })

lookupVar :: Monad m => ExprVar -> ExpressionT m (Maybe Expression)
lookupVar v = do
    m@ExprManager{..} <- get
    case Map.lookup (ELit v) indexMap of
        Nothing -> return Nothing
        Just i  -> return $ Just (Expression { eindex = i, expr = (ELit v) })

getChildren :: Monad m => Expression -> ExpressionT m [Expression]
getChildren e = do
    es <- mapM (lookupExpression . var) (children (expr e))
    return (catMaybes es)

getDependencies :: Monad m => Int -> ExpressionT m (Set.Set Int)
getDependencies i = do
    ExprManager{..} <- get
    return $ fromMaybe Set.empty (Map.lookup i depMap)

foldlExpression :: Monad m => (a -> Expression -> a) -> a -> Expression -> ExpressionT m a
foldlExpression f x e = do
    cs <- getChildren e
    foldlM (foldlExpression f) (f x e) cs

foldrExpression :: Monad m => (Expression -> a -> a) -> a -> Expression -> ExpressionT m a
foldrExpression f x e = do
    cs <- getChildren e
    foldlM (foldrExpression f) (f e x) cs

traverseExpression :: Monad m => (ExprVar -> ExprVar) -> Expression -> ExpressionT m Expression
traverseExpression f e = do
    let signs = map sign (children (expr e))
    cs <- getChildren e
    cs' <- mapM (traverseExpression f) cs
    let cs'' = map (uncurry Var) (zip signs (map eindex cs'))
    addExpression (applyToVars f (expr e) cs'')
    where
        applyToVars f (ELit v) _ = ELit (f v)
        applyToVars f x ncs      = setChildren x ncs

setRank :: Monad m => Int -> Expression -> ExpressionT m Expression
setRank r = traverseExpression (setVarRank r)
    
setVarRank r v = v {rank = r}

setHatVar :: Monad m => Expression -> ExpressionT m Expression
setHatVar = traverseExpression setVarHat

setVarHat v = if varsect v == UContVar || varsect v == ContVar
                then v {varname = varname v ++ "_hat", varsect = HatVar}
                else v

unrollExpression :: Monad m => Expression -> ExpressionT m Expression
unrollExpression = traverseExpression shiftVar

shiftVar v = v {rank = rank v + 1}

liftConjuncts Expression { expr = (EConjunct vs) }  = vs
liftConjuncts Expression { eindex = i }              = [Var Pos i]

liftDisjuncts Expression { expr = (EDisjunct vs) }  = vs
liftDisjuncts Expression { eindex = i }              = [Var Pos i]

-- |The 'conjunct' function takes a list of Expressions and produces one conjunction Expression
conjunct :: Monad m => [Expression] -> ExpressionT m Expression
conjunct []     = addExpression EFalse
conjunct (e:[]) = return e
conjunct es     = addExpression (EConjunct (concatMap liftConjuncts es))

-- |The 'disjunct' function takes a list of Expressions and produces one disjunction Expression
disjunct :: Monad m => [Expression] -> ExpressionT m Expression
disjunct []     = addExpression ETrue
disjunct (e:[]) = return e
disjunct es     = addExpression (EDisjunct (concatMap liftDisjuncts es))

makeSignsFromValue :: Int -> Int -> [Sign]
makeSignsFromValue v sz = map f [0..(sz-1)]
    where
        f b = if testBit v b then Pos else Neg

equalsConstant :: Monad m => [ExprVar] -> Int -> ExpressionT m Expression
equalsConstant es const = do
    let signs = makeSignsFromValue const (length es)
    lits <- mapM literal es
    addExpression (EConjunct (zipWith Var signs (map eindex lits)))

equate :: Monad m => Expression -> Expression -> ExpressionT m Expression
equate a b = do
    addExpression (EEquals (Var Pos (eindex a)) (Var Pos (eindex b)))

implicate :: Monad m => Expression -> Expression -> ExpressionT m Expression
implicate a b = do
    addExpression (EDisjunct [Var Neg (eindex a), Var Pos (eindex b)])

negation :: Monad m => Expression -> ExpressionT m Expression
negation x = do
    addExpression (ENot (Var Pos (eindex x)))

trueExpr :: Monad m => ExpressionT m Expression
trueExpr = addExpression ETrue

falseExpr :: Monad m => ExpressionT m Expression
falseExpr = addExpression EFalse

literal :: Monad m => ExprVar -> ExpressionT m Expression
literal = addExpression . ELit

data CopyTree = CopyTree {
      copyId        :: Int
    , dontRename    :: [Int]
    , expressions   :: Set.Set Int
    , childCopies   :: [CopyTree]
} deriving (Show, Eq)

emptyCopyTree id r = CopyTree {
      copyId        = id
    , dontRename    = r
    , expressions   = Set.empty
    , childCopies   = []
}

insertNode t n = t { childCopies = childCopies t ++ [n] }

insertExpression t e = t { expressions = Set.insert e (expressions t) }

unTree t = (copyId t, Set.toList (expressions t)) : concatMap unTree (childCopies t)

partitionCopies :: MonadIO m => Int -> ExpressionT m CopyTree
partitionCopies i = do
    ds              <- getDependencies i
    copies          <- getCopies
    let es          = Set.filter (\x -> not (x `elem` copies)) ds
    let depCopies   = filter (\x -> Set.member x ds && x /= i) copies
    ccs             <- mapM partitionCopies depCopies

    (Just e)        <- lookupExpression i
    case expr e of
        (ECopy c dr _) -> do
            let (sc, dc)    = partition (\ct -> copyId ct == c) ccs
            dr' <- mapM lookupVar dr
            return $ CopyTree {
                  copyId        = c
                , dontRename    = map eindex (catMaybes dr')
                , expressions   = Set.unions ((Set.delete i es) : (map expressions sc) ++ (map (Set.fromList . dontRename) sc))
                , childCopies   = dc ++ concatMap childCopies sc
            }
        noncopy -> do
            let (sc, dc)    = partition (\ct -> copyId ct == 0) ccs
            return $ CopyTree {
                  copyId        = 0
                , dontRename    = []
                , expressions   = Set.unions (es : map expressions sc ++ map (Set.fromList . dontRename) sc)
                , childCopies   = dc ++ concatMap childCopies sc
            }

pushUpNoRenames :: CopyTree -> (Set.Set Int, CopyTree)
pushUpNoRenames t = (push, t { expressions = left, childCopies = tc })
    where
        (pushed, tc)    = unzip $ map pushUpNoRenames (childCopies t)
        (push, left)    = Set.partition isNoRename (Set.unions ((expressions t) : pushed))
        isNoRename e    = e `elem` (dontRename t)

baseExpr e = case expr e of
    (ECopy c _ v)   -> (c, var v)
    _               -> (0, eindex e)

linkNoRenames :: [((Int, Int), Int)] -> CopyTree -> ([(Int, Int)], [((Int, Int), Int)])
linkNoRenames dMap t = (push', dMap' ++ pdMap)
    where
        recur           = map (linkNoRenames dMap) (childCopies t)
        isNoRename e    = e `elem` (dontRename t)
        (pushed, cdm)   = unzip recur
        (kp, fp)        = partition (\(c, i) -> isNoRename i) (concat pushed)
        push            = Set.filter isNoRename (expressions t)
        push'           = map (\e -> (copyId t, e)) (Set.toList push) ++ kp ++ map (\(_, e) -> (copyId t, e)) kp
        dMap'           = dMap ++ concat cdm
        pdMap           = map (\(c, i) -> ((c, i), fromJust (lookup (copyId t, i) dMap'))) fp

toDimacs :: MonadIO m => Maybe [Assignment] -> Expression -> ExpressionT m (Map.Map (Int, Int) Int, [Int], [[Int]])
toDimacs a e = do
    (dMap, es, dm)  <- makeDMap e
    avs             <- maybeM [] (mapM assignmentToVar) a

    let ad  = filter (isJust . fst) $ map (\v -> (Map.lookup (0, (var v)) dMap, v)) avs
    let as  = map (\(Just d, v) -> if sign v == Pos then d else -d) ad

    dimacs <- concatMapM (exprToDimacs dMap) es

    let (Just de) = Map.lookup (baseExpr e) dMap
    return $ (dMap, as, [de] : dm ++ dimacs)

makeDMap e = do
    ct                      <- partitionCopies (eindex e)
    let (_, copyTree)       = pushUpNoRenames ct
    let exprs               = ungroupZip (unTree copyTree)

    ExprManager{ dCache }   <- get
    let (dMap', new, dm)    = findCached dCache exprs
    let (_, dMap)           = linkNoRenames dMap' ct
    return (Map.fromList dMap, new, dm)

findCached :: DimacsCache -> [(CopyId, ExprId)] -> ([((CopyId, ExprId), Int)], [((CopyId, ExprId), Int)], [[Int]])
findCached dCache es = (dMap ++ new, new, dimacs)
    where
        lookups             = zip es (map (`lookupCache` dCache) es)
        (found, notfound)   = partition (isJust . snd) lookups
        new                 = zip (map fst notfound) [(nextDimacsId dCache)..]
        dMap                = map (mapSnd (fst . fromJust)) found
        dimacs              = concatMap (snd . fromJust . snd) found

lookupCache :: (CopyId, ExprId) -> DimacsCache -> Maybe (Int, [[Int]])
lookupCache e ((Map.lookup e) . dMap -> Just d) = Just d
lookupCache e (childCache -> Just c)            = lookupCache e c
lookupCache e _                                 = Nothing

nextDimacsId :: DimacsCache -> Int
nextDimacsId (childCache -> Just c) = nextDimacsId c
nextDimacsId (dMax -> i)            = i + 1

insertCache :: (CopyId, ExprId) -> Int -> [[Int]] -> DimacsCache -> DimacsCache
insertCache ei di d dc@(childCache -> Just c)   = dc { childCache = Just (insertCache ei di d c) }
insertCache ei di d dc                          = dc {  dMap = Map.insert ei (di, d) (dMap dc),
                                                        dMax = max di (dMax dc)
                                                     }

addToCache :: MonadIO m => (CopyId, ExprId) -> Int -> [[Int]] -> ExpressionT m ()
addToCache ei di d = do
    m <- get
    put m { dCache = insertCache ei di d (dCache m) }

exprToDimacs m ((c, e), ind) = do
    mgr         <- get
    (Just e')   <- lookupExpression e
    cs          <- mapM (makeChildVar (copies mgr) m c) (children (expr e'))
    let dimacs  = makeDimacs (expr e') ind cs

    addToCache (c, e) ind dimacs
    return dimacs

makeChildVar copies m c (Var s i) = do
    -- If the var is a copy we need to skip past it
    if i `elem` copies
    then do
        (Just e)            <- lookupExpression i
        let (ECopy c' d v)  = expr e
        (Var s' i')         <- makeChildVar copies m c' v
        return $ Var (if (s == s') then Pos else Neg) i'
    else 
        let (Just i') = Map.lookup (c, i) m in return $ Var s i'

makeDimacs :: Expr -> Int -> [Var] -> [[Int]]
makeDimacs e i cs = case e of
    (ETrue)         -> [[i]]
    (EFalse)        -> [[-i]]
    (ENot _)        -> [[-i, -(lit x)], [i, (lit x)]]
    (ELit _)        -> []
    (EEquals _ _)   -> [[-i, -(lit a), (lit b)], [-i, (lit a), -(lit b)],
                        [i, (lit a), (lit b)], [i, -(lit a), -(lit b)]]
    (EConjunct _)   -> (i : (map (negate . lit) cs)) : (map (\c -> [-i, (lit c)]) cs)
    (EDisjunct _)   -> (-i : map lit cs) : (map (\c -> [i, -(lit c)]) cs)
    (ECopy _ _ _)   -> error "Copy in makeDimacs"
    where
        (x:_)   = cs
        (a:b:_) = cs
    
printExpression :: Monad m => Expression -> ExpressionT m String
printExpression = printExpression' 0 ""

printExpression' tabs s e = do
    cs <- getChildren e
    let signs = map (\c -> if sign c == Pos then "" else "-") (children (expr e))
    pcs <- mapM (uncurry (printExpression' (tabs+1))) (zip signs cs)
    let t = concat (replicate tabs "  ")
    return $ t ++ s ++ case expr e of
        (ETrue)         -> "T"
        (EFalse)        -> "F"
        (EConjunct _)   -> "conj {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        (EDisjunct _)   -> "disj {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        (EEquals _ _)   -> "eq {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        (ENot _)        -> "not {\n"++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}" 
        (ECopy c d _)   -> "copy " ++ show c ++ " {" ++ head pcs ++ "}"
        (ELit v)        -> show v

makeCopy :: Monad m => Int -> [ExprVar] -> Expression -> ExpressionT m Expression
makeCopy c d e = do
    m@ExprManager{..} <- get
    let newCopy = c
    e' <- addExpression (ECopy newCopy d (Var Pos (eindex e)))

    m <- get
    put m { copies = (eindex e') : copies }

    return e'

getCopies :: Monad m => ExpressionT m [Int]
getCopies = do
    m <- get
    return (copies m)

-- |Contructs an assignment from a model-var pair
makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

-- |Constructs an expression from assignments
assignmentToExpression :: Monad m => [Assignment] -> ExpressionT m Expression
assignmentToExpression as = do
    vs <- mapM assignmentToVar as
    addExpression (EConjunct vs)

blockAssignment :: Monad m => [Assignment] -> ExpressionT m Expression
blockAssignment as = do
    vs <- mapM (assignmentToVar . flipAssignment) as
    addExpression (EDisjunct vs)

assignmentToVar :: Monad m => Assignment -> ExpressionT m Var
assignmentToVar (Assignment s v) = do
    e <- addExpression (ELit v)
    return $ Var s (eindex e)
