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
    , getChildren
    , getDependencies
    , lookupExpression
    , lookupVar
    , unrollExpression
    , setRank
    , setHatVar
    , conjunct
    , conjunctTemp
    , disjunct
    , equate
    , implicate
    , negation
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
} deriving (Eq)

data CopyManager = CopyManager {
      maxIndex      :: ExprId
---    , nextIndex     :: ExprId
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
}

emptyCopyManager mi = CopyManager {
      maxIndex      = mi
---    , nextIndex     = mi
    , exprMap       = IMap.empty
    , depMap        = IMap.empty
    , indexMap      = Map.empty
    , stepCache     = Map.empty
    , moveCache     = Map.empty
    , dimacsCache   = IMap.empty
}

getCopyManager :: MonadIO m => Int -> ExpressionT m CopyManager
getCopyManager c = do
    ExprManager{..} <- get
    return $ fromMaybe (emptyCopyManager 7) (IMap.lookup c copyManagers)

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
    maybeM Nothing lookupExpression ei

cacheMove :: MonadIO m => (MoveCacheType, [Assignment]) -> Expression -> ExpressionT m ()
cacheMove mi e = do
    cm@CopyManager{..} <- getCopyManager 0
    setCopyManager 0 (cm { moveCache = Map.insert mi (eindex e) moveCache })

getCachedMove :: MonadIO m => (MoveCacheType, [Assignment]) -> ExpressionT m (Maybe Expression)
getCachedMove mi = do
    cm@CopyManager{..} <- getCopyManager 0
    let ei = Map.lookup mi moveCache
    maybeM Nothing lookupExpression ei

insertExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
insertExpression c e = do
    cm@CopyManager{..} <- getCopyManager c
    let i = maxIndex
    deps <- childDependencies e

    setCopyManager c $ cm {
        maxIndex    = maxIndex+1,
---        nextIndex   = nextIndex+1,
        exprMap     = IMap.insert i e exprMap,
        depMap      = IMap.insert i (ISet.insert i deps) depMap,
        indexMap    = Map.insert e i indexMap
    }

    return $ Expression { eindex = i, expr = e }

insertExpressionWithId :: MonadIO m => Int -> ExprId -> Expr -> ExpressionT m Expression
insertExpressionWithId c i e = do
    cm@CopyManager{..} <- getCopyManager c
    deps <- childDependencies e

    setCopyManager c $ cm {
        exprMap     = IMap.insert i e exprMap,
        depMap      = IMap.insert i (ISet.insert i deps) depMap,
        indexMap    = Map.insert e i indexMap
    }
    return $ Expression { eindex = i, expr = e }

addExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
addExpression _ ETrue   = return $ Expression { eindex = 1, expr = ETrue }
addExpression _ EFalse  = return $ Expression { eindex = 2, expr = EFalse }
addExpression c e       = do
    cm@CopyManager{..} <- getCopyManager c
    case Map.lookup e indexMap of
        Nothing -> do
            insertExpression c e
        Just i -> do
            return $ Expression { eindex = i, expr = e }

addTempExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
addTempExpression mc e = do
    m@ExprManager{..} <- get
    cm <- getCopyManager mc
    let i = fromMaybe (maxIndex cm) tempMaxIndex
    deps <- childDependencies e

    put m {
        tempMaxIndex    = Just (i+1),
        tempExprs       = IMap.insert i e tempExprs,
        tempDepMap      = IMap.insert i (ISet.insert i deps) tempDepMap
    }
    return $ Expression { eindex = i, expr = e }

childDependencies e = do
    deps <- mapM (getDependencies . var) (children e)
    return $ ISet.unions deps

lookupExpression :: MonadIO m => Int -> ExpressionT m (Maybe Expression)
lookupExpression i = do
    ExprManager{..} <- get
    let maxCopies = IMap.size copyManagers
    mapMUntilJust (\c -> lookupExpressionC c i) [0..maxCopies]

lookupExpressionC :: MonadIO m => Int -> ExprId -> ExpressionT m (Maybe Expression)
lookupExpressionC c i = do
    CopyManager{..} <- getCopyManager c
    case (IMap.lookup i exprMap) of
        Nothing     -> return Nothing
        (Just exp)  -> return $ Just (Expression { eindex = i, expr = exp })

lookupVar :: MonadIO m => ExprVar -> ExpressionT m (Maybe Expression)
lookupVar v = do
    ExprManager{..} <- get
    let maxCopies = IMap.size copyManagers
    mapMUntilJust (\c -> lookupVarC c v) [0..maxCopies]

lookupVarC :: MonadIO m => Int -> ExprVar -> ExpressionT m (Maybe Expression)
lookupVarC c v = do
    CopyManager{..} <- getCopyManager c
    case (Map.lookup (ELit v) indexMap) of
        Nothing     -> return Nothing
        (Just i)    -> return $ Just (Expression { eindex = i, expr = ELit v })

getChildren :: MonadIO m => Expression -> ExpressionT m [Expression]
getChildren e = do
    es <- mapM (lookupExpression . var) (children (expr e))
    return (catMaybes es)

getDependenciesC :: MonadIO m => Int -> Int -> ExpressionT m (Maybe ISet.IntSet)
getDependenciesC c i = do
    CopyManager{..} <- getCopyManager c
    return $ IMap.lookup i depMap

getDependencies :: MonadIO m => Int -> ExpressionT m ISet.IntSet
getDependencies i = do
    ExprManager{..} <- get
    let maxCopies = IMap.size copyManagers
    deps <- mapMUntilJust (\c -> getDependenciesC c i) [0..maxCopies]
    return $ fromMaybe ISet.empty deps

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
    e' <- addExpression 0 (ELit (f v))
    return (pool, Map.insert (eindex e) (eindex e') doneMap)
tryToApply f (pool, doneMap) e = do
    let cs = children (expr e)
    let ds = map (\v -> Map.lookup (var v) doneMap) cs
    if (all isJust ds)
    then do
        let ds' = zipWith (\(Just v) (Var s _) -> Var s v) ds cs
        e' <- addExpression 0 (setChildren (expr e) ds')
        return (pool, Map.insert (eindex e) (eindex e') doneMap)
    else return (e : pool, doneMap)

setRank :: MonadIO m => Int -> Expression -> ExpressionT m Expression
setRank r = traverseExpression2 (setVarRank r)
    
setVarRank r v = v {rank = r}

setHatVar :: MonadIO m => Expression -> ExpressionT m Expression
setHatVar = traverseExpression2 setVarHat

setVarHat v = if varsect v == UContVar || varsect v == ContVar
                then v {varname = varname v ++ "_hat", varsect = HatVar}
                else v

unrollExpression :: MonadIO m => Expression -> ExpressionT m Expression
unrollExpression = traverseExpression2 shiftVar

shiftVar v = v {rank = rank v + 1}

liftConjuncts Expression { expr = (EConjunct vs) }  = vs
liftConjuncts Expression { expr = ETrue }           = []
liftConjuncts Expression { eindex = i }             = [Var Pos i]

liftDisjuncts Expression { expr = (EDisjunct vs) }  = vs
liftDisjuncts Expression { expr = EFalse }          = []
liftDisjuncts Expression { eindex = i }             = [Var Pos i]

-- |The 'conjunct' function takes a list of Expressions and produces one conjunction Expression
conjunct :: MonadIO m => [Expression] -> ExpressionT m Expression
conjunct []     = addExpression 0 EFalse
conjunct (e:[]) = return e
conjunct es     = addExpression 0 (EConjunct (concatMap liftConjuncts es))

conjunctTemp :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
conjunctTemp mc []      = addTempExpression mc EFalse
conjunctTemp mc (e:[])  = return e
conjunctTemp mc es      = addTempExpression mc (EConjunct (concatMap liftConjuncts es))

-- |The 'disjunct' function takes a list of Expressions and produces one disjunction Expression
disjunct :: MonadIO m => [Expression] -> ExpressionT m Expression
disjunct []     = addExpression 0 ETrue
disjunct (e:[]) = return e
disjunct es     = addExpression 0 (EDisjunct (concatMap liftDisjuncts es))

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
implicate a b = do
    addExpression 0 (EDisjunct [Var Neg (eindex a), Var Pos (eindex b)])

negation :: MonadIO m => Expression -> ExpressionT m Expression
negation x = do
    addExpression 0 (ENot (Var Pos (eindex x)))

trueExpr :: MonadIO m => ExpressionT m Expression
trueExpr = addExpression 0 ETrue

falseExpr :: MonadIO m => ExpressionT m Expression
falseExpr = addExpression 0 EFalse

literal :: MonadIO m => ExprVar -> ExpressionT m Expression
literal = addExpression 0 . ELit

getMaxId :: MonadIO m => ExpressionT m Int
getMaxId = do
    cm <- getCopyManager 0
    return (maxIndex cm)

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

-- |Contructs an assignment from a model-var pair
makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

-- |Constructs an expression from assignments
assignmentToExpression :: MonadIO m => [Assignment] -> ExpressionT m Expression
assignmentToExpression as = do
    vs <- mapM assignmentToVar as
    addExpression 0 (EConjunct vs)

blockAssignment :: MonadIO m => [Assignment] -> ExpressionT m Expression
blockAssignment as = do
    vs <- mapM (assignmentToVar . flipAssignment) as
    addExpression 0 (EDisjunct vs)

assignmentToVar :: MonadIO m => Assignment -> ExpressionT m Var
assignmentToVar (Assignment s v) = do
    e <- addExpression 0 (ELit v)
    return $ Var s (eindex e)

lookupDimacs :: MonadIO m => Int -> ExpressionT m (Maybe [SV.Vector CInt])
lookupDimacs i = do
    ExprManager{..} <- get
    let maxCopies = IMap.size copyManagers
    mapMUntilJust (\c -> lookupDimacsC c i) [0..maxCopies]

lookupDimacsC :: MonadIO m => Int -> ExprId -> ExpressionT m (Maybe [SV.Vector CInt])
lookupDimacsC c i = do
    CopyManager{..} <- getCopyManager c
    return $ IMap.lookup i dimacsCache

getCachedStepDimacs :: MonadIO m => Expression -> ExpressionT m [SV.Vector CInt]
getCachedStepDimacs e = do
    --WIP (doesn't work because steps get merged into other conjuncts)
---    ds              <- getDependencies (exprIndex e)
---    steps           <- (liftM ISet.fromList) getStepExprs
---    let stepsInExpr = ISet.toList (ISet.intersection ds steps)
---    mgr             <- get
---    let cachedSteps = map (\x -> (x, mgrILookup dimacsCache x (Just mgr))) stepsInExpr
---    stepDeps        <- (liftM ISet.unions) (mapM getDependencies stepsInExpr)
---    leftovers       <- mapM lookupExpression (ISet.toList (ISet.difference ds stepDeps))
---    let (cached, notcached) = partition (isJust . snd) cachedSteps
---    newlycached     <- forM notcached $ \nc -> do
---        (Just nce) <- lookupExpression (fst nc)
---        let v = makeVector nce
---        --Cache here
---        m <- get
---        put $ m { dimacsCache = IMap.insert (eindex nce) v (dimacsCache m) }
---        return v

---    return $ concatMap (fromJust . snd) cached 
---        ++ concatMap (makeVector . fromJust) leftovers 
---        ++ concat newlycached

    ds          <- (liftM ISet.toList) $ getDependencies (exprIndex e)
    mgr         <- get
    cached      <- mapM lookupDimacs ds
    let (cs, ncs) = partition (isJust . snd) (zip ds cached)
    new <- forM ncs $ \i -> do
        (Just e) <- lookupExpression (fst i)
        let v = makeVector e
        cm <- getCopyManager 0
        setCopyManager 0 (cm { dimacsCache = IMap.insert (eindex e) v (dimacsCache cm) })
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
