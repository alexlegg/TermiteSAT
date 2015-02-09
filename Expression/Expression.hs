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
    , Expr(..)

    , clearTempExpressions
    , initManager
    , initCopyMaps
    , setAssignmentRankCopy
    , cacheStep
    , getCached
    , cacheMove
    , getCachedMove
    , exprIndex
    , exprType
    , exprChildren
    , flipSign
    , emptyManager
    , getDependencies
    , lookupVar
    , unrollExpression
    , setRank
    , setHatVar
    , conjunct
    , conjunctC
    , conjunctTemp
    , disjunct
    , disjunctC
    , disjunctTemp
    , equate
    , implicate
    , implicateC
    , implicateTemp
    , negation
    , negationC
    , negationTemp
    , equalsConstant
    , trueExpr
    , falseExpr
    , literal
    , getMaxId
    , setCopy
    , printExpression
    , makeAssignment
    , assignmentToExpression
    , blockAssignment
    , assignmentToVar
    , setVarRank
    , getCachedStepDimacs
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
import qualified Data.Vector.Storable as SV
import Foreign.C.Types

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

exprType :: Expression -> Expr
exprType = expr

children :: Expr -> [Var]
children (ETrue)            = []
children (EFalse)           = []
children (ELit _)           = []
children (ENot v)           = [v]
children (EEquals x y)      = [x, y]
children (EConjunct vs)     = vs
children (EDisjunct vs)     = vs

exprChildren :: Expr -> [Var]
exprChildren = children

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
      copyManagers  :: IMap.IntMap CopyManager
    , tempMaxIndex  :: Maybe ExprId
    , tempExprs     :: IMap.IntMap Expr
    , tempDepMap    :: IMap.IntMap ISet.IntSet
    , variables     :: Set.Set ExprVar
    , mgrMaxIndices :: Int
} deriving (Eq)

data CopyManager = CopyManager {
      maxIndex      :: ExprId
    , nextIndex     :: ExprId
    , exprMap       :: IMap.IntMap Expr
    , depMap        :: IMap.IntMap ISet.IntSet
    , indexMap      :: Map.Map Expr ExprId
    , stepCache     :: Map.Map (Int, Int, Int, Int, Int) ExprId
    , moveCache     :: Map.Map (MoveCacheType, [Assignment]) ExprId
    , dimacsCache   :: IMap.IntMap [SV.Vector CInt]
} deriving (Eq)

data Section = StateVar | ContVar | UContVar | HatVar
    deriving (Show, Eq, Ord)

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

setAssignmentRankCopy :: Assignment -> Int -> Int -> Assignment
setAssignmentRankCopy (Assignment s v) r c = Assignment s (v { rank = r, ecopy = c })

emptyManager = ExprManager { 
      copyManagers  = IMap.empty
    , tempMaxIndex  = Nothing
    , tempExprs     = IMap.empty
    , tempDepMap    = IMap.empty
    , variables     = Set.empty
    , mgrMaxIndices = 200
}

emptyCopyManager mi incr = CopyManager {
      maxIndex      = mi + incr
    , nextIndex     = mi + 1
    , exprMap       = IMap.empty
    , depMap        = IMap.empty
    , indexMap      = Map.empty
    , stepCache     = Map.empty
    , moveCache     = Map.empty
    , dimacsCache   = IMap.empty
}

clearTempExpressions :: MonadIO m => ExpressionT m ()
clearTempExpressions = do
    m <- get
    put m { tempMaxIndex = Nothing, tempExprs = IMap.empty, tempDepMap = IMap.empty }

-- |Call this function once the base formula is loaded
initManager :: MonadIO m => ExpressionT m ()
initManager = do
    m@ExprManager{..} <- get
    let (Just c0) = IMap.lookup 0 copyManagers
    put $ m { mgrMaxIndices = 3 * nextIndex c0 }
    setCopyManager 0 (c0 { maxIndex = maxIndex c0 * 3 })

-- |Call this function with the max copy you will use before constructing expressions
initCopyMaps :: MonadIO m => Int -> ExpressionT m ()
initCopyMaps mc = do
    mapM_ initCopyMap [1..mc]

-- Copy all variables into a copy map first
initCopyMap c = do
    ExprManager{..} <- get
    let vars = Set.toList variables
    mapM_ (addExpression c . f) vars
    where
        f v = ELit (v { ecopy = c })

getCopyManager :: MonadIO m => Int -> ExpressionT m CopyManager
getCopyManager c = do
    ExprManager{..} <- get
    case (IMap.lookup c copyManagers) of
        Just cm -> return cm
        Nothing -> do
            fillCopyManagers c
            ExprManager{..} <- get
            let (Just cm) = IMap.lookup c copyManagers
            return cm
            
fillCopyManagers c = do
    prevIndex <- if c == 0
        then return 3
        else fillCopyManagers (c-1)

    mgr@ExprManager{..} <- get
    case (IMap.lookup c copyManagers) of
        Just cm -> return (maxIndex cm)
        Nothing -> do
            let newManager = emptyCopyManager prevIndex mgrMaxIndices
            put $ mgr { copyManagers = IMap.insert c newManager copyManagers }
            return (maxIndex newManager)

setCopyManager :: MonadIO m => Int -> CopyManager -> ExpressionT m ()
setCopyManager c cm = do
    m@(ExprManager{..}) <- get
    put $ m { copyManagers = IMap.insert c cm copyManagers }

cacheStep :: MonadIO m => Int -> Int -> Int -> Int -> Int -> Expression -> ExpressionT m ()
cacheStep r pc c1 c2 t e = do
    let copy = maximum [pc, c1, c2]
    cm <- getCopyManager copy
    setCopyManager copy (cm { stepCache = Map.insert (r, pc, c1, c2, t) (eindex e) (stepCache cm) })

getCached :: MonadIO m => Int -> Int -> Int -> Int -> Int -> ExpressionT m (Maybe Expression)
getCached r pc c1 c2 t = do
    let copy = maximum [pc, c1, c2]
    cm <- getCopyManager copy
    let ei = Map.lookup (r, pc, c1, c2, t) (stepCache cm)
    maybeM Nothing (lookupExpression copy) ei

cacheMove :: MonadIO m => Int -> (MoveCacheType, [Assignment]) -> Expression -> ExpressionT m ()
cacheMove mc mi e = do
    cm@CopyManager{..} <- getCopyManager mc
    setCopyManager mc (cm { moveCache = Map.insert mi (eindex e) moveCache })

getCachedMove :: MonadIO m => Int -> (MoveCacheType, [Assignment]) -> ExpressionT m (Maybe Expression)
getCachedMove copy mi = do
    cm@CopyManager{..} <- getCopyManager copy
    let ei = Map.lookup mi moveCache
    maybeM Nothing (lookupExpression copy) ei

insertExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
insertExpression _ (ELit v) = do
    when (ecopy v == 0) $ do
        m <- get
        put m { variables = Set.insert v (variables m) }

    insertExpression' 0 (ELit v)
insertExpression c e        = insertExpression' c e

insertExpression' c e = do
    cm@CopyManager{..} <- getCopyManager c
    let i = nextIndex

    when (i >= maxIndex) $ do
        --Throw away all copy managers > c
        mgr <- get
        let maxCopies = IMap.size (copyManagers mgr)
        when (c+1 < maxCopies) $ liftIO $ putStrLn ("Flushing managers: " ++ show (c+1) ++ " - " ++ show maxCopies)
        let copyManagers' = IMap.filterWithKey (\k _ -> k <= c) (copyManagers mgr)
        put $ mgr { copyManagers = copyManagers' }
        setCopyManager c $ cm { maxIndex = maxIndex + (mgrMaxIndices mgr)}
        clearTempExpressions

    cm@CopyManager{..} <- getCopyManager c
    deps <- childDependencies c e
    setCopyManager c $ cm {
        nextIndex   = nextIndex+1,
        exprMap     = IMap.insert i e exprMap,
        depMap      = IMap.insert i (ISet.insert i deps) depMap,
        indexMap    = Map.insert e i indexMap
    }

    return $ Expression { eindex = i, expr = e }

lookupExprIndex :: MonadIO m => Int -> Expr -> ExpressionT m (Maybe Int)
lookupExprIndex 0 e   = do
    cm@CopyManager{..} <- getCopyManager 0
    return $ Map.lookup e indexMap
lookupExprIndex mc e  = do
    ei <- lookupExprIndex (mc-1) e
    case ei of
        Nothing -> do
            cm@CopyManager{..} <- getCopyManager mc
            return $ Map.lookup e indexMap
        x       -> return x

addExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
addExpression _ ETrue   = return $ Expression { eindex = 1, expr = ETrue }
addExpression _ EFalse  = return $ Expression { eindex = 2, expr = EFalse }
addExpression c e       = do
    mgr <- get
    ei <- lookupExprIndex c e

    case ei of
        Nothing -> do
            insertExpression c e
        Just i -> do
            return $ Expression { eindex = i, expr = e }

addTempExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
addTempExpression mc e = do
    m@ExprManager{..} <- get
    cm <- getCopyManager mc
    let i = fromMaybe (maxIndex cm + 1) tempMaxIndex
    deps <- childDependencies mc e

    put m {
        tempMaxIndex    = Just (i+1),
        tempExprs       = IMap.insert i e tempExprs,
        tempDepMap      = IMap.insert i (ISet.insert i deps) tempDepMap
    }
    return $ Expression { eindex = i, expr = e }

childDependencies mc e = do
    ExprManager{..} <- get
    deps <- mapM (getDependencies mc . var) (children e)
    return $ ISet.unions deps

lookupExpression :: MonadIO m => Int -> Int -> ExpressionT m (Maybe Expression)
lookupExpression mc i = do
    ExprManager{..} <- get
    e <- mapMUntilJust (\c -> lookupExpressionC c i) [0..mc]
    if isNothing e
    then case (IMap.lookup i tempExprs) of
        Nothing     -> return Nothing
        (Just exp)  -> return $ Just (Expression { eindex = i, expr = exp })
    else return e

lookupExpressionC :: MonadIO m => Int -> ExprId -> ExpressionT m (Maybe Expression)
lookupExpressionC c i = do
    CopyManager{..} <- getCopyManager c
    case (IMap.lookup i exprMap) of
        Nothing     -> return Nothing
        (Just exp)  -> return $ Just (Expression { eindex = i, expr = exp })

lookupExpressionC' :: MonadIO m => Int -> ExprId -> ExpressionT m (Maybe (Expression, Int))
lookupExpressionC' c i = do
    exp <- lookupExpressionC c i
    case exp of
        Nothing     -> return Nothing
        (Just e)    -> return $ Just (e, c)

lookupExpressionAndCopy :: MonadIO m => Int -> Int -> ExpressionT m (Maybe (Expression, Int))
lookupExpressionAndCopy mc i = do
    ExprManager{..} <- get
    e <- mapMUntilJust (\c -> lookupExpressionC' c i) [0..mc]
    if isNothing e
    then case (IMap.lookup i tempExprs) of
        Nothing     -> return Nothing
        (Just exp)  -> return $ Just ((Expression { eindex = i, expr = exp }), -1)
    else return e

lookupVar :: MonadIO m => ExprVar -> ExpressionT m (Maybe Expression)
lookupVar v = do
    ExprManager{..} <- get
    let maxCopies = IMap.size copyManagers
    vs <- mapM (\c -> lookupVarC c v) [0..(maxCopies-1)]
    let vsj = catMaybes vs
    case vsj of
        []      -> return $ Nothing
        (x:[])  -> return $ Just x
        xs      -> throwError $ "multiple vars: " ++ show xs

lookupVarC :: MonadIO m => Int -> ExprVar -> ExpressionT m (Maybe Expression)
lookupVarC c v = do
    CopyManager{..} <- getCopyManager c
    case (Map.lookup (ELit v) indexMap) of
        Nothing     -> return Nothing
        (Just i)    -> return $ Just (Expression { eindex = i, expr = ELit v })

getDependenciesC :: MonadIO m => Int -> Int -> ExpressionT m (Maybe ISet.IntSet)
getDependenciesC c i = do
    CopyManager{..} <- getCopyManager c
    return $ IMap.lookup i depMap

getDependencies :: MonadIO m => Int -> Int -> ExpressionT m ISet.IntSet
getDependencies mc i = do
    ExprManager{..} <- get
    deps <- mapMUntilJust (\c -> getDependenciesC c i) [0..mc]
    if isNothing deps
        then return $ fromMaybe ISet.empty (IMap.lookup i tempDepMap)
        else return $ fromMaybe ISet.empty deps

---traverseExpression :: MonadIO m => (ExprVar -> ExprVar) -> Expression -> ExpressionT m Expression
---traverseExpression f e = do
---    let signs = map sign (children (expr e))
---    cs <- getChildren e
---    cs' <- mapM (traverseExpression f) cs
---    let cs'' = map (uncurry Var) (zip signs (map eindex cs'))
---    addExpression 0 (applyToVars f (expr e) cs'')
---    where
---        applyToVars f (ELit v) _ = ELit (f v)
---        applyToVars f x ncs      = setChildren x ncs

traverseExpression2 :: MonadIO m => Int -> (ExprVar -> ExprVar) -> Expression -> ExpressionT m Expression
traverseExpression2 mc f e = do
    ds  <- getDependencies mc (eindex e)
    when (ISet.null ds) $ throwError "Empty dependencies"
    es  <- (liftM catMaybes) $ mapM (lookupExpression mc) (ISet.toList ds)
    done <- applyTraverse mc f es Map.empty
    let (Just e') = Map.lookup (eindex e) done
    liftM fromJust $ lookupExpression mc e'

applyTraverse :: MonadIO m => Int -> (ExprVar -> ExprVar) -> [Expression] -> Map.Map Int Int -> ExpressionT m (Map.Map Int Int)
applyTraverse mc _ [] done = return done
applyTraverse mc f pool done = do
    (pool', done') <- foldlM (tryToApply mc f) ([], done) pool
    applyTraverse mc f pool' done'

tryToApply :: MonadIO m => Int -> (ExprVar -> ExprVar) -> ([Expression], Map.Map Int Int) -> Expression -> ExpressionT m ([Expression], Map.Map Int Int)
tryToApply mc f (pool, doneMap) e@(expr -> ELit v)  = do
    e' <- addExpression mc (ELit (f v))
    return (pool, Map.insert (eindex e) (eindex e') doneMap)
tryToApply mc f (pool, doneMap) e = do
    let cs = children (expr e)
    let ds = map (\v -> Map.lookup (var v) doneMap) cs
    if (all isJust ds)
    then do
        let ds' = zipWith (\(Just v) (Var s _) -> Var s v) ds cs
        e' <- addExpression mc (setChildren (expr e) ds')
        return (pool, Map.insert (eindex e) (eindex e') doneMap)
    else return (e : pool, doneMap)

setRank :: MonadIO m => Int -> Expression -> ExpressionT m Expression
setRank r = traverseExpression2 0 (setVarRank r)
    
setVarRank r v = v {rank = r}

setHatVar :: MonadIO m => Int -> Expression -> ExpressionT m Expression
setHatVar mc = traverseExpression2 mc setVarHat

setVarHat v = if varsect v == UContVar || varsect v == ContVar
                then v {varname = varname v ++ "_hat", varsect = HatVar}
                else v

unrollExpression :: MonadIO m => Expression -> ExpressionT m Expression
unrollExpression = traverseExpression2 0 shiftVar

shiftVar v = v {rank = rank v + 1}

liftConjuncts Expression { expr = (EConjunct vs) }  = vs
liftConjuncts Expression { expr = ETrue }           = []
liftConjuncts Expression { eindex = i }             = [Var Pos i]

liftDisjuncts Expression { expr = (EDisjunct vs) }  = vs
liftDisjuncts Expression { expr = EFalse }          = []
liftDisjuncts Expression { eindex = i }             = [Var Pos i]

-- |The 'conjunct' function takes a list of Expressions and produces one conjunction Expression
conjunct :: MonadIO m => [Expression] -> ExpressionT m Expression
conjunct = conjunctC 0

conjunctC :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
conjunctC c []      = addExpression c EFalse
conjunctC c (e:[])  = return e
conjunctC c es      = addExpression c (EConjunct (concatMap liftConjuncts es))

conjunctTemp :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
conjunctTemp mc []      = addTempExpression mc EFalse
conjunctTemp mc (e:[])  = return e
conjunctTemp mc es      = addTempExpression mc (EConjunct (concatMap liftConjuncts es))

-- |The 'disjunct' function takes a list of Expressions and produces one disjunction Expression
disjunct :: MonadIO m => [Expression] -> ExpressionT m Expression
disjunct = disjunctC 0

disjunctC :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
disjunctC c []      = addExpression c ETrue
disjunctC c (e:[])  = return e
disjunctC c es      = addExpression c (EDisjunct (concatMap liftDisjuncts es))

disjunctTemp :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
disjunctTemp mc []      = addTempExpression mc ETrue
disjunctTemp mc (e:[])  = return e
disjunctTemp mc es      = addTempExpression mc (EDisjunct (concatMap liftDisjuncts es))

makeSignsFromValue :: Int -> Int -> [Sign]
makeSignsFromValue v sz = map f [0..(sz-1)]
    where
        f b = if testBit v b then Pos else Neg

equalsConstant :: MonadIO m => [ExprVar] -> Int -> ExpressionT m Expression
equalsConstant es const = do
    let signs = makeSignsFromValue const (length es)
    lits <- mapM literal es
    addExpression 0 (EConjunct (zipWith Var signs (map eindex lits)))

equate :: MonadIO m => Expression -> Expression -> ExpressionT m Expression
equate a b = do
    addExpression 0 (EEquals (Var Pos (eindex a)) (Var Pos (eindex b)))

implicate :: MonadIO m => Expression -> Expression -> ExpressionT m Expression
implicate = implicateC 0

implicateC :: MonadIO m => Int -> Expression -> Expression -> ExpressionT m Expression
implicateC c a b = addExpression 0 (EDisjunct [Var Neg (eindex a), Var Pos (eindex b)])

implicateTemp :: MonadIO m => Int -> Expression -> Expression -> ExpressionT m Expression
implicateTemp mc a b = addTempExpression mc (EDisjunct [Var Neg (eindex a), Var Pos (eindex b)])

negation :: MonadIO m => Expression -> ExpressionT m Expression
negation = negationC 0

negationC :: MonadIO m => Int -> Expression -> ExpressionT m Expression
negationC c x = addExpression c (ENot (Var Pos (eindex x)))

negationTemp :: MonadIO m => Int -> Expression -> ExpressionT m Expression
negationTemp mc x = do
    addTempExpression mc (ENot (Var Pos (eindex x)))

trueExpr :: MonadIO m => ExpressionT m Expression
trueExpr = addExpression 0 ETrue

falseExpr :: MonadIO m => ExpressionT m Expression
falseExpr = addExpression 0 EFalse

literal :: MonadIO m => ExprVar -> ExpressionT m Expression
literal = addExpression 0 . ELit

getMaxId :: MonadIO m => ExpressionT m Int
getMaxId = do
    ExprManager{..} <- get
    return $ fromJust tempMaxIndex  

getChildren :: MonadIO m => Expression -> ExpressionT m [Expression]
getChildren e = do
    ExprManager{..} <- get
    let mc = IMap.size copyManagers
    es <- mapM (lookupExpression (mc-1) . var) (children (expr e))
    return (catMaybes es)

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
setCopy cMap e = traverseExpression2 mc f e
    where
        f v = v { ecopy = fromMaybe (ecopy v) (Map.lookup (varsect v, rank v) cMap) }
        mc  = maximum (Map.elems cMap)

-- |Contructs an assignment from a model-var pair
makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

-- |Constructs an expression from assignments
assignmentToExpression :: MonadIO m => Int -> [Assignment] -> ExpressionT m Expression
assignmentToExpression c as = do
    vs <- mapM (assignmentToVar c) as
    addExpression c (EConjunct vs)

blockAssignment :: MonadIO m => Int -> [Assignment] -> ExpressionT m Expression
blockAssignment c as = do
    vs <- mapM (assignmentToVar c . flipAssignment) as
    addExpression c (EDisjunct vs)

assignmentToVar :: MonadIO m => Int -> Assignment -> ExpressionT m Var
assignmentToVar c (Assignment s v) = do
    e <- addExpression c (ELit v)
    return $ Var s (eindex e)

lookupDimacs :: MonadIO m => Int -> Int -> ExpressionT m (Maybe [SV.Vector CInt])
lookupDimacs mc i = do
    if mc == 0
    then mapMUntilJust (\c -> lookupDimacsC c i) [0..mc]
    else return Nothing

lookupDimacsC :: MonadIO m => Int -> ExprId -> ExpressionT m (Maybe [SV.Vector CInt])
lookupDimacsC c i = do
    CopyManager{..} <- getCopyManager c
    return $ IMap.lookup i dimacsCache

getCachedStepDimacs :: MonadIO m => Int -> Expression -> ExpressionT m [SV.Vector CInt]
getCachedStepDimacs mc e = do
    ds          <- (liftM ISet.toList) $ getDependencies mc (exprIndex e)
    mgr         <- get
    cached      <- mapM (lookupDimacs mc) ds
    let (cs, ncs) = partition (isJust . snd) (zip ds cached)
    new <- forM ncs $ \i -> do
---        (Just (e, c)) <- lookupExpressionAndCopy mc (fst i)
        blah <- lookupExpressionAndCopy mc (fst i)

        when (blah == Nothing) $ do
            liftIO $ putStrLn (show (fst i))
            blah <- lookupExpressionAndCopy 1 (fst i)
            liftIO $ putStrLn (show blah)
            throwError $ "Expression not found"
        let (Just (e, c)) = blah
        let v = makeVector e
---        when (c == 0) $ do
---            cm <- getCopyManager 0
---            setCopyManager 0 (cm { dimacsCache = IMap.insert (eindex e) v (dimacsCache cm) })
---            return ()
---        when (c == 1) $ do
---            cm <- getCopyManager 0
---            setCopyManager 0 (cm { dimacsCache = IMap.insert (eindex e) v (dimacsCache cm) })
---            return ()
        return v

    return $ concat new ++ concatMap (fromJust . snd) cs

makeVector :: Expression -> [SV.Vector CInt]
makeVector e = case exprType e of
    (ETrue)         -> [(SV.singleton i)]
    (EFalse)        -> [(SV.singleton (-i))]
    (ENot _)        -> [ SV.fromList [-i, -(litc x)]
                       , SV.fromList [i, (litc x)]]
    (ELit _)        -> []
    (EEquals _ _)   -> [ SV.fromList [-i, -(litc a), (litc b)]
                       , SV.fromList [-i, (litc a), -(litc b)]
                       , SV.fromList [i, (litc a), (litc b)]
                       , SV.fromList [i, -(litc a), -(litc b)]]
    (EConjunct _)   -> SV.fromList (i : (map (negate . litc) cs)) : (map (\c -> SV.fromList [-i, (litc c)]) cs)
    (EDisjunct _)   -> SV.fromList (-i : map litc cs) : (map (\c -> SV.fromList [i, -(litc c)]) cs)
    where
        i       = fromIntegral $ exprIndex e
        cs      = exprChildren (exprType e)
        (x:_)   = cs
        (a:b:_) = exprChildren (exprType e)
        litc (Var Pos v) = fromIntegral v
        litc (Var Neg v) = fromIntegral (-v)
