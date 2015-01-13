{-# LANGUAGE RecordWildCards, ViewPatterns, NamedFieldPuns #-}
module Expression.Expression (
      ExpressionT(..)
    , ExprVar(..)
    , Expression
    , Section(..)
    , Sign(..)
    , Var(..)
    , Assignment(..)
    , MoveCacheType(..)

    , setAssignmentRankCopy
    , pushManager
    , popManager
    , stopDuplicateChecking
    , cacheStep
    , getCached
    , cacheMove
    , getCachedMove
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
    , conjunctQuick
    , disjunct
    , equate
    , implicate
    , negation
    , equalsConstant
    , trueExpr
    , falseExpr
    , literal
    , toDimacs
    , getMaxId
    , setCopy
    , setCopyAll
    , setCopyStep
    , printExpression
    , makeAssignment
    , assignmentToExpression
    , blockAssignment
    , setVarRank
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.ST.Safe
import qualified Data.Map.Strict as Map
import qualified Data.IntMap as IMap
import qualified Data.Set as Set
import qualified Data.IntSet as ISet
import Data.List
import Data.Bits (testBit)
import Data.Foldable (foldlM)
import Data.Maybe
import Utils.Utils
import Debug.Trace

type ExpressionT m = StateT ExprManager (EitherT String m)

throwError :: MonadIO m => String -> ExpressionT m a
throwError = lift . left

type CopyId = Int
type ExprId = Int

data ExprVar = ExprVar {
      varname   :: String
    , varsect   :: Section
    , bit       :: Int
    , rank      :: Int
    , ecopy     :: Int
    } deriving (Eq, Ord)

instance Show ExprVar where
    show v = let ExprVar{..} = v in varname ++ show rank ++ "_" ++ show ecopy ++ "[" ++ show bit ++ "]"

data Var = Var Sign ExprId deriving (Show, Eq, Ord)

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
            | EEquals Var Var
            | EConjunct [Var]
            | EDisjunct [Var]
            deriving (Eq, Ord, Show)

data Expression = Expression {
      eindex    :: ExprId
    , expr      :: Expr
    } deriving (Eq, Ord, Show)

exprIndex :: Expression -> Int
exprIndex = eindex

children :: Expr -> [Var]
children (ETrue)            = []
children (EFalse)           = []
children (ELit _)           = []
children (ENot v)           = [v]
children (EEquals x y)      = [x, y]
children (EConjunct vs)     = vs
children (EDisjunct vs)     = vs

setChildren :: Expr -> [Var] -> Expr
setChildren (ETrue) _           = ETrue
setChildren (EFalse) _          = EFalse
setChildren (ELit l) _          = ELit l
setChildren (ENot _) (v:[])     = ENot v
setChildren (ENot _) []         = error $ "ENot of empty list"
setChildren (EEquals _ _) vs    = let (x:y:[]) = vs in EEquals x y
setChildren (EConjunct _) vs    = EConjunct vs
setChildren (EDisjunct _) vs    = EDisjunct vs

data MoveCacheType = RegularMove | HatMove | BlockedState deriving (Show, Eq, Ord)

data ExprManager = ExprManager {
      maxIndex      :: ExprId
    , exprMap       :: IMap.IntMap Expr
    , depMap        :: IMap.IntMap ISet.IntSet
    , indexMap      :: Map.Map Expr ExprId
    , stepCache     :: Map.Map (Int, Int, Int, Int, Int) ExprId
    , moveCache     :: Map.Map (MoveCacheType, [Assignment]) ExprId
    , parentMgr     :: Maybe ExprManager
    , checkDupes    :: Bool
} deriving (Eq)

data Section = StateVar | ContVar | UContVar | HatVar
    deriving (Show, Eq, Ord)

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

setAssignmentRankCopy :: Assignment -> Int -> Int -> Assignment
setAssignmentRankCopy (Assignment s v) r c = Assignment s (v { rank = r, ecopy = c })

emptyManager = ExprManager { 
                  maxIndex      = 3
                , exprMap       = IMap.empty
                , depMap        = IMap.empty
                , indexMap      = Map.empty
                , stepCache     = Map.empty
                , moveCache     = Map.empty
                , parentMgr     = Nothing
                , checkDupes    = True
                }

pushManager :: MonadIO m => ExpressionT m ()
pushManager = do
    m@ExprManager{..} <- get
    put $ emptyManager {
          maxIndex      = maxIndex
        , parentMgr     = Just m
        , checkDupes    = checkDupes
        }

popManager :: MonadIO m => ExpressionT m ()
popManager = do
    ExprManager{..} <- get
    put (fromJust parentMgr)

stopDuplicateChecking :: MonadIO m => ExpressionT m ()
stopDuplicateChecking = do
    m <- get
    put m { checkDupes = False }

mgrLookup :: Ord a => (ExprManager -> Map.Map a b) -> a -> (Maybe ExprManager) -> (Maybe b)
mgrLookup lMap k (Just mgr) = maybe (mgrLookup lMap k (parentMgr mgr)) Just (Map.lookup k (lMap mgr))
mgrLookup lMap k Nothing    = Nothing

mgrLookup2 :: Ord a => (ExprManager -> Map.Map a b) -> a -> (Maybe ExprManager) -> (Maybe b)
mgrLookup2 lMap k (Just mgr) = maybe (mgrLookup2 lMap k (parentMgr mgr)) Just (Map.lookup k (lMap mgr))
mgrLookup2 lMap k Nothing    = Nothing

mgrLookup3 :: Ord a => (ExprManager -> Map.Map a b) -> a -> (Maybe ExprManager) -> (Maybe b)
mgrLookup3 lMap k (Just mgr) = maybe (mgrLookup3 lMap k (parentMgr mgr)) Just (Map.lookup k (lMap mgr))
mgrLookup3 lMap k Nothing    = Nothing

mgrILookup :: (ExprManager -> IMap.IntMap a) -> Int -> (Maybe ExprManager) -> (Maybe a)
mgrILookup lMap k (Just mgr)    = maybe (mgrILookup lMap k (parentMgr mgr)) Just (IMap.lookup k (lMap mgr))
mgrILookup lMap k Nothing       = Nothing

cacheStep :: MonadIO m => (Int, Int, Int, Int, Int) -> Expression -> ExpressionT m ()
cacheStep ni e = do
    m <- get
    put $ m { stepCache = Map.insert ni (eindex e) (stepCache m) }

getCached :: MonadIO m => (Int, Int, Int, Int, Int) -> ExpressionT m (Maybe Expression)
getCached i = do
    m <- get
    let ei = mgrLookup stepCache i (Just m)
---    trace (if isNothing ei then "cache miss" else "cache hit") $ maybeM Nothing lookupExpression ei
    maybeM Nothing lookupExpression ei

cacheMove :: MonadIO m => (MoveCacheType, [Assignment]) -> Expression -> ExpressionT m ()
cacheMove mi e = do
    m <- get
    put m { moveCache = Map.insert mi (eindex e) (moveCache m) }

getCachedMove :: MonadIO m => (MoveCacheType, [Assignment]) -> ExpressionT m (Maybe Expression)
getCachedMove mi = do
    m <- get
    let ei = mgrLookup moveCache mi (Just m)
    maybeM Nothing lookupExpression ei

insertExpression :: MonadIO m => Expr -> ExpressionT m Expression
insertExpression e = do
    m@ExprManager{..} <- get
    let i = maxIndex
    deps <- childDependencies e
    put m {
        maxIndex    = maxIndex+1,
        exprMap     = IMap.insert i e exprMap,
        depMap      = IMap.insert i (ISet.insert i deps) depMap,
        indexMap    = Map.insert e i indexMap}
    return $ Expression { eindex = i, expr = e }

insertExpressionWithId :: MonadIO m => ExprId -> Expr -> ExpressionT m Expression
insertExpressionWithId i e = do
    m@ExprManager{..} <- get
    deps <- childDependencies e
    put m {
        exprMap     = IMap.insert i e exprMap,
        depMap      = IMap.insert i (ISet.insert i deps) depMap,
        indexMap    = Map.insert e i indexMap}
    return $ Expression { eindex = i, expr = e }

addExpression :: MonadIO m => Expr -> ExpressionT m Expression
addExpression ETrue     = return $ Expression { eindex = 1, expr = ETrue }
addExpression EFalse    = return $ Expression { eindex = 2, expr = EFalse }
addExpression e         = do
    m <- get
    if checkDupes m
    then do
        case mgrLookup2 indexMap e (Just m) of
            Nothing -> do
                insertExpression e
            Just i -> do
                return $ Expression { eindex = i, expr = e }
    else insertExpression e

childDependencies e = do
    m <- get
    let cs = children e
    let deps = map (\x -> mgrILookup depMap (var x) (Just m)) cs
    return $ ISet.unions (ISet.fromList (map var (children e)) : catMaybes deps)

lookupExpression :: MonadIO m => Int -> ExpressionT m (Maybe Expression)
lookupExpression i = do
    mgr <- get
    case (mgrILookup exprMap i (Just mgr)) of
        Nothing     -> return Nothing
        (Just exp)  -> return $ Just (Expression { eindex = i, expr = exp })

lookupVar :: MonadIO m => ExprVar -> ExpressionT m (Maybe Expression)
lookupVar v = do
    mgr <- get
    case mgrLookup indexMap (ELit v) (Just mgr) of
        Nothing -> return Nothing
        Just i  -> return $ Just (Expression { eindex = i, expr = (ELit v) })

getChildren :: MonadIO m => Expression -> ExpressionT m [Expression]
getChildren e = do
    es <- mapM (lookupExpression . var) (children (expr e))
    return (catMaybes es)

getDependencies :: MonadIO m => Int -> ExpressionT m ISet.IntSet
getDependencies i = do
    mgr <- get
    return $ fromMaybe ISet.empty (mgrILookup depMap i (Just mgr))

foldlExpression :: MonadIO m => (a -> Expression -> a) -> a -> Expression -> ExpressionT m a
foldlExpression f x e = do
    cs <- getChildren e
    foldlM (foldlExpression f) (f x e) cs

foldrExpression :: MonadIO m => (Expression -> a -> a) -> a -> Expression -> ExpressionT m a
foldrExpression f x e = do
    cs <- getChildren e
    foldlM (foldrExpression f) (f e x) cs

traverseExpression :: MonadIO m => (ExprVar -> ExprVar) -> Expression -> ExpressionT m Expression
traverseExpression f e = do
    let signs = map sign (children (expr e))
    cs <- getChildren e
    cs' <- mapM (traverseExpression f) cs
    let cs'' = map (uncurry Var) (zip signs (map eindex cs'))
    addExpression (applyToVars f (expr e) cs'')
    where
        applyToVars f (ELit v) _ = ELit (f v)
        applyToVars f x ncs      = setChildren x ncs

-- ############################ This seems to be slower??
traverseExpression2 :: MonadIO m => (ExprVar -> ExprVar) -> Expression -> ExpressionT m Expression
traverseExpression2 f e = do
    ds  <- getDependencies (eindex e)
    es  <- (liftM catMaybes) $ mapM lookupExpression (ISet.toList ds)
    done <- applyTraverse f es Map.empty
    let (Just e') = Map.lookup (eindex e) done
    liftM fromJust $ lookupExpression e'

applyTraverse :: MonadIO m => (ExprVar -> ExprVar) -> [Expression] -> Map.Map Int Int -> ExpressionT m (Map.Map Int Int)
applyTraverse _ [] done = return done
applyTraverse f pool done = do
    (pool', done') <- foldlM (tryToApply f) ([], done) pool
    applyTraverse f pool' done'

tryToApply :: MonadIO m => (ExprVar -> ExprVar) -> ([Expression], Map.Map Int Int) -> Expression -> ExpressionT m ([Expression], Map.Map Int Int)
tryToApply f (pool, doneMap) e@(expr -> ELit v)  = do
    e' <- addExpression (ELit (f v))
    return (pool, Map.insert (eindex e) (eindex e') doneMap)
tryToApply f (pool, doneMap) e = do
    let cs = children (expr e)
    let ds = map (\v -> Map.lookup (var v) doneMap) cs
    if (all isJust ds)
    then do
        let ds' = zipWith (\(Just v) (Var s _) -> Var s v) ds cs
        e' <- addExpression (setChildren (expr e) ds')
        return (pool, Map.insert (eindex e) (eindex e') doneMap)
    else return (e : pool, doneMap)
-- ##########################################################

setRank :: MonadIO m => Int -> Expression -> ExpressionT m Expression
setRank r = traverseExpression2 (setVarRank r)
    
setVarRank r v = v {rank = r}

setHatVar :: MonadIO m => Expression -> ExpressionT m Expression
setHatVar = traverseExpression2 setVarHat

setVarHat v = if varsect v == UContVar || varsect v == ContVar
                then v {varname = varname v ++ "_hat", varsect = HatVar}
                else v

unrollExpression :: MonadIO m => Expression -> ExpressionT m Expression
unrollExpression = traverseExpression shiftVar

shiftVar v = v {rank = rank v + 1}

liftConjuncts Expression { expr = (EConjunct vs) }  = vs
liftConjuncts Expression { expr = ETrue }           = []
liftConjuncts Expression { eindex = i }             = [Var Pos i]

liftDisjuncts Expression { expr = (EDisjunct vs) }  = vs
liftDisjuncts Expression { expr = EFalse }          = []
liftDisjuncts Expression { eindex = i }             = [Var Pos i]

-- |The 'conjunct' function takes a list of Expressions and produces one conjunction Expression
conjunct :: MonadIO m => [Expression] -> ExpressionT m Expression
conjunct []     = addExpression EFalse
conjunct (e:[]) = return e
conjunct es     = addExpression (EConjunct (concatMap liftConjuncts es))

conjunctQuick :: MonadIO m => [Expression] -> ExpressionT m Expression
conjunctQuick []        = addExpression EFalse
conjunctQuick (e:[])    = return e
conjunctQuick es        = insertExpression (EConjunct (concatMap liftConjuncts es))

-- |The 'disjunct' function takes a list of Expressions and produces one disjunction Expression
disjunct :: MonadIO m => [Expression] -> ExpressionT m Expression
disjunct []     = addExpression ETrue
disjunct (e:[]) = return e
disjunct es     = addExpression (EDisjunct (concatMap liftDisjuncts es))

makeSignsFromValue :: Int -> Int -> [Sign]
makeSignsFromValue v sz = map f [0..(sz-1)]
    where
        f b = if testBit v b then Pos else Neg

equalsConstant :: MonadIO m => [ExprVar] -> Int -> ExpressionT m Expression
equalsConstant es const = do
    let signs = makeSignsFromValue const (length es)
    lits <- mapM literal es
    addExpression (EConjunct (zipWith Var signs (map eindex lits)))

equate :: MonadIO m => Expression -> Expression -> ExpressionT m Expression
equate a b = do
    addExpression (EEquals (Var Pos (eindex a)) (Var Pos (eindex b)))

implicate :: MonadIO m => Expression -> Expression -> ExpressionT m Expression
implicate a b = do
    addExpression (EDisjunct [Var Neg (eindex a), Var Pos (eindex b)])

negation :: MonadIO m => Expression -> ExpressionT m Expression
negation x = do
    addExpression (ENot (Var Pos (eindex x)))

trueExpr :: MonadIO m => ExpressionT m Expression
trueExpr = addExpression ETrue

falseExpr :: MonadIO m => ExpressionT m Expression
falseExpr = addExpression EFalse

literal :: MonadIO m => ExprVar -> ExpressionT m Expression
literal = addExpression . ELit

toDimacs :: MonadIO m => Maybe [Assignment] -> Expression -> ExpressionT m ([Int], [[Int]])
toDimacs a e = do
    ds      <- getDependencies (eindex e)
    es      <- (liftM catMaybes) $ mapM lookupExpression (ISet.toList ds)
    avs     <- maybeM [] (mapM assignmentToVar) a
    let as  = map (\a -> if sign a == Pos then var a else -(var a)) avs
    let dm  = concatMap makeDimacs es
    return $ (as, [eindex e] : dm)

getMaxId :: MonadIO m => ExpressionT m Int
getMaxId = do
    ExprManager{..} <- get
    return maxIndex

makeDimacs :: Expression -> [[Int]]
makeDimacs e = case expr e of
    (ETrue)         -> [[i]]
    (EFalse)        -> [[-i]]
    (ENot _)        -> [[-i, -(lit x)], [i, (lit x)]]
    (ELit _)        -> []
    (EEquals _ _)   -> [[-i, -(lit a), (lit b)], [-i, (lit a), -(lit b)],
                        [i, (lit a), (lit b)], [i, -(lit a), -(lit b)]]
    (EConjunct _)   -> (i : (map (negate . lit) cs)) : (map (\c -> [-i, (lit c)]) cs)
    (EDisjunct _)   -> (-i : map lit cs) : (map (\c -> [i, -(lit c)]) cs)
    where
        i       = eindex e
        cs      = children (expr e)
        (x:_)   = cs
        (a:b:_) = children (expr e)

printExpression :: MonadIO m => Expression -> ExpressionT m String
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
        (ELit v)        -> show v

setCopy :: MonadIO m => (Map.Map (Section, Int) Int) -> Expression -> ExpressionT m Expression
setCopy cMap e = traverseExpression2 f e
    where
        f v = v { ecopy = fromMaybe (ecopy v) (Map.lookup (varsect v, rank v) cMap) }

setCopyAll :: MonadIO m => Int -> Expression -> ExpressionT m Expression
setCopyAll copy e = traverseExpression f e
    where
        f v = v { ecopy = copy }

setCopyStep :: MonadIO m => (Map.Map (Section, Int) Int) -> Expression -> ExpressionT m Expression
setCopyStep cMap e = copyTraverse f e
    where
        f v = v { ecopy = fromMaybe (ecopy v) (Map.lookup (varsect v, rank v) cMap) }

copyTraverse :: MonadIO m => (ExprVar -> ExprVar) -> Expression -> ExpressionT m Expression
copyTraverse f e = do
    ds          <- (liftM ISet.toList) $ getDependencies (eindex e)
    eds         <- mapM (liftM fromJust . lookupExpression) ds
    cs          <- mapM (makeCopy f) eds
    let cMap    = Map.fromList cs
    mapM_ (copyExpression cMap f) ds

    let ei'     = Map.lookup (eindex e) cMap
    (Just e')   <- lookupExpression (fromJust ei')
    return e'

makeCopy :: MonadIO m => (ExprVar -> ExprVar) -> Expression -> ExpressionT m (ExprId, ExprId)
makeCopy f e@(expr -> ELit v) = do
    e' <- addExpression (ELit (f v))
    return (eindex e, eindex e')
makeCopy _ e = do
    m@ExprManager{..} <- get
    put m { maxIndex = maxIndex + 1 }
    return (eindex e, maxIndex)


copyExpression :: MonadIO m => Map.Map ExprId ExprId -> (ExprVar -> ExprVar) -> ExprId -> ExpressionT m ()
copyExpression cMap f i = do
    (Just e) <- lookupExpression i
    case (expr e) of
        (ELit v)    -> do
            return ()
        ex          -> do
            let expr'       = setChildren ex (map (replaceVar cMap) (children ex)) 
            let (Just i')   = Map.lookup i cMap
            insertExpressionWithId i' expr'
            return ()

replaceVar cMap (Var s i) = Var s (fromJust (Map.lookup i cMap))

-- |Contructs an assignment from a model-var pair
makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

-- |Constructs an expression from assignments
assignmentToExpression :: MonadIO m => [Assignment] -> ExpressionT m Expression
assignmentToExpression as = do
    vs <- mapM assignmentToVar as
    addExpression (EConjunct vs)

blockAssignment :: MonadIO m => [Assignment] -> ExpressionT m Expression
blockAssignment as = do
    vs <- mapM (assignmentToVar . flipAssignment) as
    addExpression (EDisjunct vs)

assignmentToVar :: MonadIO m => Assignment -> ExpressionT m Var
assignmentToVar (Assignment s v) = do
    e <- addExpression (ELit v)
    return $ Var s (eindex e)
