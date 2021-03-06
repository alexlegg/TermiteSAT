{-# LANGUAGE RecordWildCards, ViewPatterns, NamedFieldPuns #-}
module Expression.Expression (
      ExpressionT
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
    , lookupVar
    , lookupVarName
    , lookupExpression
    , unrollExpression
    , foldExpression
    , foldExpressionM
    , foldExpressionIO
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
    , makeAssignmentValue
    , assignmentToExpression
    , blockAssignment
    , assignmentToVar
    , setVarRank
    , getCachedStepDimacs
    , flipAssignment
    , assignmentSection
    , assignmentRank
    , assignmentCopy
    , getVars
    , makeSignsFromValue
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map.Strict as Map
import qualified Data.IntMap as IMap
import qualified Data.Set as Set
import qualified Data.IntSet as ISet
import Data.List
import Data.Bits (testBit)
import Data.Foldable (foldlM)
import Data.Maybe
import Utils.Utils
import qualified Data.Vector.Storable as SV
import Foreign.C.Types

type ExpressionT m = StateT ExprManager (EitherT String m)

throwError :: MonadIO m => String -> ExpressionT m a
throwError s = lift (left ("ERROR: " ++ s))

type ExprId = Int

data ExprVar = ExprVar {
      varname   :: String
    , varsect   :: Section
    , bit       :: Int
    , rank      :: Int
    , ecopy     :: Int
    , varAIG    :: Maybe Int
    } deriving (Eq, Ord)

instance Show ExprVar where
    show v = let ExprVar{..} = v in varname ++ show rank ++ "_" ++ show ecopy ++ "[" ++ show bit ++ "]"

data Var = Var Sign ExprId deriving (Show, Eq, Ord)

var :: Var -> ExprId
var (Var _ v)   = v

sign :: Var -> Sign
sign (Var s _)  = s

data Sign = Pos | Neg deriving (Show, Eq, Ord)

flipSign :: Sign -> Sign
flipSign Pos = Neg
flipSign Neg = Pos

flipAssignment :: Assignment -> Assignment
flipAssignment (Assignment s v) = Assignment (flipSign s) v

assignmentSection :: Assignment -> Section
assignmentSection (Assignment _ v)  = varsect v

assignmentRank :: Assignment -> Int
assignmentRank (Assignment _ v)     = rank v

assignmentCopy :: Assignment -> Int
assignmentCopy (Assignment _ v)     = ecopy v

data Expr   = ETrue
            | EFalse
            | ELit ExprVar
            | ENot Var
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
children (EConjunct vs)     = vs
children (EDisjunct vs)     = vs

exprChildren :: Expr -> [Var]
exprChildren = children

setChildren :: Expr -> [Var] -> Expr
setChildren (ETrue) _           = ETrue
setChildren (EFalse) _          = EFalse
setChildren (ELit l) _          = ELit l
setChildren (ENot _) (v:[])     = ENot v
setChildren (ENot _) _          = error $ "ENot on non-singleton"
setChildren (EConjunct _) vs    = EConjunct vs
setChildren (EDisjunct _) vs    = EDisjunct vs

data MoveCacheType = RegularMove Int | HatMove Int | BlockedState | UnWinState deriving (Show, Eq, Ord)

data ExprManager = ExprManager {
      copyManagers  :: IMap.IntMap CopyManager
    , tempMaxIndex  :: Maybe ExprId
    , tempExprs     :: IMap.IntMap Expr
    , tempDepMap    :: IMap.IntMap ISet.IntSet
    , tempParentMap :: IMap.IntMap ISet.IntSet
    , variables     :: Set.Set ExprVar
    , mgrMaxIndices :: Int
} deriving (Eq)

data CopyManager = CopyManager {
      maxIndex      :: ExprId
    , nextIndex     :: ExprId
    , indexPool     :: ISet.IntSet
    , exprMap       :: IMap.IntMap Expr
    , depMap        :: IMap.IntMap ISet.IntSet
    , parentMap     :: IMap.IntMap ISet.IntSet
    , indexMap      :: Map.Map Expr ExprId
    , stepCache     :: Map.Map (Int, Int, Int, Int, Int) ExprId
    , moveCache     :: Map.Map (MoveCacheType, [Assignment]) ExprId
    , dimacsCache   :: IMap.IntMap [SV.Vector CInt]
    , copyVars      :: Map.Map Int ExprVar
} deriving (Eq)

data Section = StateVar | ContVar | UContVar | HatVar
    deriving (Show, Eq, Ord)

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

instance Show Assignment where
    show (Assignment Pos v) = show v
    show (Assignment Neg v) = '-' : show v

setAssignmentRankCopy :: Assignment -> Int -> Int -> Assignment
setAssignmentRankCopy (Assignment s v) r c = Assignment s (v { rank = r, ecopy = c })

emptyManager :: ExprManager
emptyManager = ExprManager { 
      copyManagers  = IMap.empty
    , tempMaxIndex  = Nothing
    , tempExprs     = IMap.empty
    , tempDepMap    = IMap.empty
    , tempParentMap = IMap.empty
    , variables     = Set.empty
    , mgrMaxIndices = 200
}

emptyCopyManager :: Int -> Int -> CopyManager
emptyCopyManager mi incr = CopyManager {
      maxIndex      = mi + incr
    , nextIndex     = mi + 1
    , indexPool     = ISet.empty
    , exprMap       = IMap.empty
    , depMap        = IMap.empty
    , parentMap     = IMap.empty
    , indexMap      = Map.empty
    , stepCache     = Map.empty
    , moveCache     = Map.empty
    , dimacsCache   = IMap.empty
    , copyVars      = Map.empty
}

clearTempExpressions :: MonadIO m => ExpressionT m ()
clearTempExpressions = do
    m <- get
    put m { tempMaxIndex = Nothing, tempExprs = IMap.empty, tempDepMap = IMap.empty }

-- |Call this function once the base formula is loaded
initManager :: MonadIO m => ExpressionT m ()
initManager = do
    m@ExprManager{..} <- get
    let (Just c0)   = IMap.lookup 0 copyManagers
    let incr        = ceiling ((fromIntegral (maxIndex c0)) * expansionFactor)
    put $ m { mgrMaxIndices = incr }
    setCopyManager 0 (c0 { maxIndex = ceiling ((fromIntegral (maxIndex c0)) * expansionFactor) })
    clearCopyManagers

expansionFactor :: Double
expansionFactor = 1.5

clearCopyManagers :: MonadIO m => ExpressionT m ()
clearCopyManagers = do
    mgr <- get
    let copyManagers' = IMap.filterWithKey (\k _ -> k == 0) (copyManagers mgr)
    put $ mgr { copyManagers = copyManagers' }

-- |Call this function with the max copy you will use before constructing expressions
initCopyMaps :: MonadIO m => Int -> ExpressionT m ()
initCopyMaps mc = do
    mapM_ initCopyMap [1..mc]

-- Copy all variables into a copy map first
initCopyMap :: MonadIO m => Int -> ExpressionT m ()
initCopyMap c = do
    ExprManager{..} <- get
    let vars = Set.toList variables
    mapM_ (addExpression c . f) vars
    where
        f v = ELit (v { ecopy = c })

getCopyManager :: MonadIO m => Int -> ExpressionT m CopyManager
getCopyManager c = do
    mgr <- get
    case (IMap.lookup c (copyManagers mgr)) of
        Just cm -> return cm
        Nothing -> do
            _ <- fillCopyManagers c
            mgr' <- get
            let (Just cm) = IMap.lookup c (copyManagers mgr')
            return cm
            
fillCopyManagers :: MonadIO m => Int -> ExpressionT m Int
fillCopyManagers c = do
    prevIndex <- if c == 0
        then return 3
        else fillCopyManagers (c-1)

    mgr@ExprManager{..} <- get
    case (IMap.lookup c copyManagers) of
        Just cm -> do
            return (maxIndex cm)
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
    CopyManager{..} <- getCopyManager copy
    let ei = Map.lookup mi moveCache
    maybeM Nothing (lookupExpression copy) ei

insertExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
insertExpression _ (ELit v) = do
    --Lits are always put into copy 0
    when (ecopy v == 0) $ do
        m <- get
        put m { variables = Set.insert v (variables m) }
    e <- insertExpression' 0 (ELit v)
    cm <- getCopyManager 0
    setCopyManager 0 (cm { copyVars = Map.insert (eindex e) v (copyVars cm)})
    return e
insertExpression c e        = insertExpression' c e

insertExpression' :: MonadIO m => Int -> Expr -> ExpressionT m Expression
insertExpression' c e = do
    cm' <- getCopyManager c

    when (nextIndex cm' >= maxIndex cm') $ do
        --Throw away all copy managers > c
        mgr <- get

        let copyManagers' = IMap.filterWithKey (\k _ -> k <= c) (copyManagers mgr)
        when (copyManagers mgr /= copyManagers') $ do
            put $ mgr { copyManagers = copyManagers' }
        setCopyManager c $ cm' { maxIndex = (maxIndex cm') + (mgrMaxIndices mgr)}
        clearTempExpressions
        return ()

    cm      <- getCopyManager c
    deps    <- childDependencies c e
    let i   = nextIndex cm
    setCopyManager c $ cm {
        nextIndex   = i + 1,
        exprMap     = IMap.insert i e (exprMap cm),
        depMap      = IMap.insert i (ISet.insert i deps) (depMap cm),
        parentMap   = IMap.insert i ISet.empty (parentMap cm),
        indexMap    = Map.insert e i (indexMap cm)
    }
    mapM_ (insertParent c i) (map var (children e))

    return $ Expression { eindex = i, expr = e }

lookupExprIndex :: MonadIO m => Int -> Expr -> ExpressionT m (Maybe Int)
lookupExprIndex 0 e   = do
    CopyManager{..} <- getCopyManager 0
    return $ Map.lookup e indexMap
lookupExprIndex mc e  = do
    ei <- lookupExprIndex (mc-1) e
    case ei of
        Nothing -> do
            CopyManager{..} <- getCopyManager mc
            return $ Map.lookup e indexMap
        x       -> return x

addExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
addExpression _ ETrue   = return $ Expression { eindex = 1, expr = ETrue }
addExpression _ EFalse  = return $ Expression { eindex = 2, expr = EFalse }
addExpression c e       = do
    ei <- lookupExprIndex c e

    case ei of
        Nothing -> do
            insertExpression c e
        Just i -> do
            return $ Expression { eindex = i, expr = e }

addTempExpression :: MonadIO m => Int -> Expr -> ExpressionT m Expression
addTempExpression mc e = do
    cm <- getCopyManager mc
    m@ExprManager{..} <- get
    let i = fromMaybe (nextIndex cm + 1) tempMaxIndex
    deps <- childDependencies mc e

    put m {
        tempMaxIndex    = Just (i+1),
        tempExprs       = IMap.insert i e tempExprs,
        tempDepMap      = IMap.insert i (ISet.insert i deps) tempDepMap,
        tempParentMap   = IMap.insert i (ISet.empty) $ foldl (\mp (Var _ x) -> IMap.adjust (ISet.insert i) x mp) tempParentMap (children e)
    }
    return $ Expression { eindex = i, expr = e }

childDependencies :: MonadIO m => Int -> Expr -> ExpressionT m ISet.IntSet
childDependencies mc e = do
    deps <- mapM (getDependencies mc . var) (children e)
    return $ ISet.unions deps

lookupExpression :: MonadIO m => Int -> Int -> ExpressionT m (Maybe Expression)
lookupExpression _ 1 = return $ Just $ Expression { eindex = 1, expr = ETrue }
lookupExpression _ 2 = return $ Just $ Expression { eindex = 2, expr = EFalse }
lookupExpression mc i = do
    e <- mapMUntilJust (\c -> lookupExpressionC c i) [0..mc]
    ExprManager{..} <- get
    if isNothing e
    then case (IMap.lookup i tempExprs) of
        Nothing     -> return Nothing
        (Just ex)   -> return $ Just (Expression { eindex = i, expr = ex })
    else return e

lookupExpressionC :: MonadIO m => Int -> ExprId -> ExpressionT m (Maybe Expression)
lookupExpressionC c i = do
    CopyManager{..} <- getCopyManager c
    case (IMap.lookup i exprMap) of
        Nothing     -> return Nothing
        (Just ex)   -> return $ Just (Expression { eindex = i, expr = ex })

lookupExpressionC' :: MonadIO m => Int -> ExprId -> ExpressionT m (Maybe (Expression, Int))
lookupExpressionC' c i = do
    ex <- lookupExpressionC c i
    case ex of
        Nothing     -> return Nothing
        (Just e)    -> return $ Just (e, c)

lookupExpressionAndCopy :: MonadIO m => Int -> Int -> ExpressionT m (Maybe (Expression, Int))
lookupExpressionAndCopy _ 1     = return $ Just $ (Expression { eindex = 1, expr = ETrue }, 0)
lookupExpressionAndCopy _ 2     = return $ Just $ (Expression { eindex = 2, expr = EFalse }, 0)
lookupExpressionAndCopy mc i    = do
    e <- mapMUntilJust (\c -> lookupExpressionC' c i) [0..mc]
    ExprManager{..} <- get
    if isNothing e
    then case (IMap.lookup i tempExprs) of
        Nothing     -> return Nothing
        (Just ex)   -> return $ Just ((Expression { eindex = i, expr = ex }), -1)
    else return e

getVars :: MonadIO m => Section -> Int -> Int -> ExpressionT m (Map.Map Int ExprVar)
getVars s r c = do
    cm <- getCopyManager 0
    let vars = Map.filter (\v -> varsect v == s && rank v == r && ecopy v == c) (copyVars cm)
    return vars

lookupVar :: MonadIO m => ExprVar -> ExpressionT m (Maybe Expression)
lookupVar v = do
    mgr <- get
    let maxCopies = IMap.size (copyManagers mgr)
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
getDependenciesC _ 1    = return $ Just (ISet.singleton 1)
getDependenciesC _ 2    = return $ Just (ISet.singleton 2)
getDependenciesC c i    = do
    CopyManager{..} <- getCopyManager c
    return $ IMap.lookup i depMap

getDependencies :: MonadIO m => Int -> Int -> ExpressionT m ISet.IntSet
getDependencies _ 1     = return $ ISet.singleton 1
getDependencies _ 2     = return $ ISet.singleton 2
getDependencies mc i    = do
    deps <- mapMUntilJust (\c -> getDependenciesC c i) [0..mc]
    ExprManager{..} <- get
    if isNothing deps
        then return $ fromMaybe ISet.empty (IMap.lookup i tempDepMap)
        else return $ fromMaybe ISet.empty deps

insertParentC :: MonadIO m => Int -> Int -> Int -> ExpressionT m (Maybe Int)
insertParentC i p c = do
    cm <- getCopyManager c
    if (isJust (IMap.lookup i (parentMap cm)))
    then do
        setCopyManager c (cm { parentMap = IMap.adjust (ISet.insert p) i (parentMap cm) })
        return (Just c)
    else return Nothing

insertParent :: MonadIO m => Int -> Int -> Int -> ExpressionT m ()
insertParent mc p i = do
    _ <- mapMUntilJust (insertParentC i p) [0..mc]
    return ()

foldExpressionM :: (MonadIO m) => Int -> (Int -> Expr -> [(Sign, a)] -> m a) -> Expression -> ExpressionT m a
foldExpressionM mc f e = do
    let cs  = children (expr e)
    ces     <- mapM (lookupExpression mc) (map var cs)
    fes     <- mapM (foldExpressionM mc f) (catMaybes ces)
    lift $ lift $ f (eindex e) (expr e) (zip (map sign cs) fes)

foldExpression :: MonadIO m => Int -> (Int -> Expr -> [(Sign, a)] -> a) -> Expression -> ExpressionT m a
foldExpression _ f (expr -> ETrue)  = return $ f 1 ETrue []
foldExpression _ f (expr -> EFalse) = return $ f 2 EFalse []
foldExpression mc f e               = do
    ds <- getDependencies mc (eindex e)
    when (ISet.null ds) $ throwError "Empty dependencies"

    es <- (liftM catMaybes) $ mapM (lookupExpression mc) (ISet.toList ds)
    done <- applyFold f es Map.empty
    let (Just r) = Map.lookup (eindex e) done
    return r

foldExpressionIO :: MonadIO m => Int -> (Int -> Expr -> [(Sign, a)] -> IO a) -> Expression -> ExpressionT m a
foldExpressionIO _ f (expr -> ETrue)    = liftIO $ f 1 ETrue []
foldExpressionIO _ f (expr -> EFalse)   = liftIO $ f 2 EFalse []
foldExpressionIO mc f e                 = do
    ds <- getDependencies mc (eindex e)
    when (ISet.null ds) $ throwError "Empty dependencies"

    es      <- (liftM catMaybes) $ mapM (lookupExpression mc) (ISet.toList ds)
    fTrue   <- liftIO $ f 1 ETrue []
    fFalse  <- liftIO $ f 2 EFalse []
    done    <- applyFoldIO f es (Map.fromList [(1, fTrue), (2, fFalse)])
    let (Just r) = Map.lookup (eindex e) done
    return r

applyFold :: MonadIO m => (Int -> Expr -> [(Sign, a)] -> a) -> [Expression] -> Map.Map Int a -> ExpressionT m (Map.Map Int a)
applyFold _ [] done = return done
applyFold f pool done = do
    (pool', done') <- foldM (tryToApply' f) ([], done) pool
    applyFold f pool' done'

applyFoldIO :: MonadIO m => (Int -> Expr -> [(Sign, a)] -> IO a) -> [Expression] -> Map.Map Int a -> ExpressionT m (Map.Map Int a)
applyFoldIO _ [] done = return done
applyFoldIO f pool done = do
    (pool', done') <- foldM (tryToApplyIO' f) ([], done) pool
    applyFoldIO f pool' done'

tryToApply' :: MonadIO m => (Int -> Expr -> [(Sign, a)] -> a) -> ([Expression], Map.Map Int a) -> Expression -> ExpressionT m ([Expression], Map.Map Int a)
tryToApply' f (pool, doneMap) e = do
    let cs = children (expr e)
    let ds = map (\v -> Map.lookup (var v) doneMap) cs
    if (all isJust ds)
    then do
        let ds' = zipWith (\(Just x) (Var s _) -> (s, x)) ds cs
        let x = f (eindex e) (expr e) ds'
        return (pool, Map.insert (eindex e) x doneMap)
    else return (e : pool, doneMap)

tryToApplyIO' :: MonadIO m => (Int -> Expr -> [(Sign, a)] -> IO a) -> ([Expression], Map.Map Int a) -> Expression -> ExpressionT m ([Expression], Map.Map Int a)
tryToApplyIO' f (pool, doneMap) e = do
    let cs = children (expr e)
    let ds = map (\v -> Map.lookup (var v) doneMap) cs
    if (all isJust ds)
    then do
        let ds' = zipWith (\(Just x) (Var s _) -> (s, x)) ds cs
        x <- liftIO $ f (eindex e) (expr e) ds'
        return (pool, Map.insert (eindex e) x doneMap)
    else return (e : pool, doneMap)

traverseExpression :: MonadIO m => Int -> (ExprVar -> ExprVar) -> Expression -> ExpressionT m Expression
traverseExpression _  _ e@(expr -> ETrue)   = return e
traverseExpression _  _ e@(expr -> EFalse)  = return e
traverseExpression mc f e                   = do
    ds  <- getDependencies mc (eindex e)
    when (ISet.null ds) $ throwError "Empty dependencies"
    es  <- (liftM catMaybes) $ mapM (lookupExpression mc) (ISet.toList ds)
    done <- applyTraverse mc f es (Map.fromList [(1, 1), (2, 2)])
    let (Just e') = Map.lookup (eindex e) done
    liftM fromJust $ lookupExpression mc e'

applyTraverse :: MonadIO m => Int -> (ExprVar -> ExprVar) -> [Expression] -> Map.Map Int Int -> ExpressionT m (Map.Map Int Int)
applyTraverse _ _ [] done = return done
applyTraverse mc f pool done = do
    (pool', done') <- foldlM (tryToApply mc f) ([], done) pool
    applyTraverse mc f pool' done'

tryToApply :: MonadIO m => Int -> (ExprVar -> ExprVar) -> ([Expression], Map.Map Int Int) -> Expression -> ExpressionT m ([Expression], Map.Map Int Int)
tryToApply mc f (pool, doneMap) e@(expr -> ELit v)  = do
    e' <- addExpression mc (ELit (f v))
    return (pool, Map.insert (eindex e) (eindex e') doneMap)
tryToApply mc _ (pool, doneMap) e = do
    let cs = children (expr e)
    let ds = map (\v -> Map.lookup (var v) doneMap) cs
    if (all isJust ds)
    then do
        let ds' = zipWith (\(Just v) (Var s _) -> Var s v) ds cs
        e' <- addExpression mc (setChildren (expr e) ds')
        return (pool, Map.insert (eindex e) (eindex e') doneMap)
    else return (e : pool, doneMap)

setRank :: MonadIO m => Int -> Expression -> ExpressionT m Expression
setRank r = traverseExpression 0 (setVarRank r)
    
setVarRank :: Int -> ExprVar -> ExprVar
setVarRank r v = v {rank = r}

setHatVar :: MonadIO m => Int -> Expression -> ExpressionT m Expression
setHatVar mc = traverseExpression mc setVarHat

setVarHat :: ExprVar -> ExprVar
setVarHat v = if varsect v == UContVar || varsect v == ContVar
                then v {varname = varname v ++ "_hat", varsect = HatVar}
                else v

unrollExpression :: MonadIO m => Expression -> ExpressionT m Expression
unrollExpression = traverseExpression 0 shiftVar

shiftVar :: ExprVar -> ExprVar
shiftVar v = v {rank = rank v + 1}

liftConjuncts :: Expression -> [Var]
liftConjuncts Expression { expr = EConjunct vs }        = vs
liftConjuncts Expression { expr = ETrue }               = []
liftConjuncts Expression { expr = ENot (Var Pos i) }    = [Var Neg i]
liftConjuncts Expression { expr = ENot (Var Neg i) }    = [Var Pos i]
liftConjuncts Expression { eindex = i }                 = [Var Pos i]

conjunct' :: MonadIO m => Int -> (Int -> Expr -> ExpressionT m Expression) -> [Expression] -> [Var] -> ExpressionT m Expression
conjunct' _ _ [] []                 = throwError "Empty conjunction"
conjunct' c f es []                 = if (all ((==) ETrue . expr) es) 
                                        then f c ETrue
                                        else throwError $ "Empty conjunction after lifting: " ++ show es
conjunct' c _ _ ((Var Pos i):[])    = (fmap fromJust) $ lookupExpression c i
conjunct' c f _ ((Var Neg i):[])    = do
    e <- (fmap fromJust) $ lookupExpression c i
    negation' c f e
conjunct' c f _ es                  = f c (EConjunct es)

-- |The 'conjunct' function takes a list of Expressions and produces one conjunction Expression
conjunct :: MonadIO m => [Expression] -> ExpressionT m Expression
conjunct = conjunctC 0

conjunctC :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
conjunctC c es = conjunct' c addExpression es (concatMap liftConjuncts es)

conjunctTemp :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
conjunctTemp mc es = conjunct' mc addTempExpression es (concatMap liftConjuncts es)

liftDisjuncts :: Expression -> [Var]
liftDisjuncts Expression {expr = (EDisjunct vs)}    = vs
liftDisjuncts Expression {expr = EFalse}            = []
liftDisjuncts Expression {expr = ENot (Var Pos i)}  = [Var Neg i]
liftDisjuncts Expression {expr = ENot (Var Neg i)}  = [Var Pos i]
liftDisjuncts Expression {eindex = i}               = [Var Pos i]

disjunct' :: MonadIO m => Int -> (Int -> Expr -> ExpressionT m Expression) -> [Expression] -> [Var] -> ExpressionT m Expression
disjunct' _ _ [] []                 = throwError $ "Empty disjunction"
disjunct' c f es []                 = if (all ((==) EFalse . expr) es) 
                                        then f c EFalse
                                        else throwError $ "Empty disjunction after lifting: " ++ show es
disjunct' c _ _ ((Var Pos i):[])    = (fmap fromJust) $ lookupExpression c i
disjunct' c f _ ((Var Neg i):[])    = do
    e <- (fmap fromJust) $ lookupExpression c i
    negation' c f e
disjunct' c f _ es                  = f c (EDisjunct es)

-- |The 'disjunct' function takes a list of Expressions and produces one disjunction Expression
disjunct :: MonadIO m => [Expression] -> ExpressionT m Expression
disjunct = disjunctC 0

disjunctC :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
disjunctC c es = disjunct' c addExpression es (concatMap liftDisjuncts es)

disjunctTemp :: MonadIO m => Int -> [Expression] -> ExpressionT m Expression
disjunctTemp mc es = disjunct' mc addTempExpression es (concatMap liftDisjuncts es)

makeSignsFromValue :: Int -> Int -> [Sign]
makeSignsFromValue v sz = map f [0..(sz-1)]
    where
        f b = if testBit v b then Pos else Neg

equalsConstant :: MonadIO m => [ExprVar] -> Int -> ExpressionT m Expression
equalsConstant es val = do
    let signs = makeSignsFromValue val (length es)
    lits <- mapM literal es
    addExpression 0 (EConjunct (zipWith Var signs (map eindex lits)))

equate :: MonadIO m => Expression -> Expression -> ExpressionT m Expression
equate a b = do
    aImpB <- addExpression 0 (EDisjunct [Var Neg (eindex a), Var Pos (eindex b)])
    bImpA <- addExpression 0 (EDisjunct [Var Pos (eindex a), Var Neg (eindex b)])
    addExpression 0 (EConjunct [Var Pos (eindex aImpB), Var Pos (eindex bImpA)])

implicate :: MonadIO m => Expression -> Expression -> ExpressionT m Expression
implicate = implicateC 0

implicateC :: MonadIO m => Int -> Expression -> Expression -> ExpressionT m Expression
implicateC c a b = addExpression c (EDisjunct [Var Neg (eindex a), Var Pos (eindex b)])

implicateTemp :: MonadIO m => Int -> Expression -> Expression -> ExpressionT m Expression
implicateTemp mc a b = addTempExpression mc (EDisjunct [Var Neg (eindex a), Var Pos (eindex b)])

negation' :: MonadIO m => Int -> (Int -> Expr -> ExpressionT m Expression) -> Expression -> ExpressionT m Expression
negation' c _ (Expression {expr = ENot (Var Pos e)})    = (fmap fromJust) $ lookupExpression c e
negation' c f (Expression {expr = EFalse})              = f c ETrue
negation' c f (Expression {expr = ETrue})               = f c EFalse
negation' c f (Expression {eindex = i})                 = f c (ENot (Var Pos i))

negation :: MonadIO m => Expression -> ExpressionT m Expression
negation = negationC 0

negationC :: MonadIO m => Int -> Expression -> ExpressionT m Expression
negationC c = negation' c addExpression

negationTemp :: MonadIO m => Int -> Expression -> ExpressionT m Expression
negationTemp c = negation' c addTempExpression

trueExpr :: MonadIO m => ExpressionT m Expression
trueExpr = addExpression 0 ETrue

falseExpr :: MonadIO m => ExpressionT m Expression
falseExpr = addExpression 0 EFalse

literal :: MonadIO m => ExprVar -> ExpressionT m Expression
literal = addExpression 0 . ELit

getMaxId :: MonadIO m => Int -> ExpressionT m Int
getMaxId mc = do
    ExprManager{..} <- get
    case tempMaxIndex of
        Nothing     -> do
            cm <- getCopyManager mc
            return $ nextIndex cm
        (Just tmi)  -> return tmi

getChildren :: MonadIO m => Expression -> ExpressionT m [Expression]
getChildren e = do
    ExprManager{..} <- get
    let mc = IMap.size copyManagers
    es <- mapM (lookupExpression (mc-1) . var) (children (expr e))
    return (catMaybes es)

printExpression :: MonadIO m => Expression -> ExpressionT m String
printExpression = printExpression' 0 ""

printExpression' :: MonadIO m => Int -> String -> Expression -> ExpressionT m String
printExpression' tabs s e = do
    cs <- getChildren e
    let signs = map (\c -> if sign c == Pos then "" else "-") (children (expr e))
    pcs <- mapM (uncurry (printExpression' (tabs+1))) (zip signs cs)
    let t = concat (replicate tabs "  ")
    return $ t ++ s ++ case expr e of
        (ETrue)         -> "T"
        (EFalse)        -> "F"
        (EConjunct _)   -> "conj (" ++ show (eindex e) ++ " {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        (EDisjunct _)   -> "disj (" ++ show (eindex e) ++ ") {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        (ENot _)        -> "not (" ++ show (eindex e) ++ ") {\n"++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}" 
        (ELit v)        -> "(" ++ show (eindex e) ++ ") " ++ show v

setCopy :: MonadIO m => (Map.Map (Section, Int) Int) -> Expression -> ExpressionT m Expression
setCopy cMap e = traverseExpression mc f e
    where
        f v = v { ecopy = fromMaybe (ecopy v) (Map.lookup (varsect v, rank v) cMap) }
        mc  = maximum (Map.elems cMap)

-- |Contructs an assignment from a model-var pair
makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

lookupVarName :: MonadIO m => String -> ExpressionT m [ExprVar]
lookupVarName name = do
    cm <- getCopyManager 0
    return $ catMaybes $ map snd $ IMap.toList $ IMap.map filterName (exprMap cm)
    where
        filterName (ELit (v@(ExprVar {varname   = n
                                    , rank      = 1}))) = if n == name then Just v else Nothing
        filterName _                                    = Nothing

makeAssignmentValue :: [ExprVar] -> Int -> [Assignment]
makeAssignmentValue vs val = zipWith Assignment signs vs
    where
        signs = makeSignsFromValue val (length vs)

-- |Constructs an expression from assignments
assignmentToExpression :: MonadIO m => Int -> [Assignment] -> ExpressionT m Expression
assignmentToExpression _ [] = trueExpr
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

cacheDimacs :: MonadIO m => Int -> Int -> [SV.Vector CInt] -> ExpressionT m ()
cacheDimacs c i v = do
    cm <- getCopyManager c
    setCopyManager c (cm { dimacsCache = IMap.insert i v (dimacsCache cm) })

lookupDimacs :: [CopyManager] -> Int -> Maybe [SV.Vector CInt]
lookupDimacs cms i = mapUntilJust (\cm -> lookupDimacsC cm i) cms

lookupDimacsC :: CopyManager -> ExprId -> Maybe [SV.Vector CInt]
lookupDimacsC cm i = IMap.lookup i (dimacsCache cm)

getCachedStepDimacs :: MonadIO m => Int -> Expression -> ExpressionT m [SV.Vector CInt]
getCachedStepDimacs mc e = do
    ds          <- (liftM ISet.toList) $ getDependencies mc (exprIndex e)
    cms         <- mapM getCopyManager [0..mc]
    let cached  = map (lookupDimacs cms) ds
    let (cs, ncs) = partition (isJust . snd) (zip ds cached)
    new <- forM ncs $ \(i, _) -> do
        (Just (ex, c)) <- lookupExpressionAndCopy mc i
        let v = makeVector ex
        when (c >= 0) $ cacheDimacs c i v
        return v

    return $ concat new ++ concatMap (fromJust . snd) cs

makeVector :: Expression -> [SV.Vector CInt]
makeVector e = case exprType e of
    (ETrue)         -> [(SV.singleton i)]
    (EFalse)        -> [(SV.singleton (-i))]
    (ENot _)        -> [ SV.fromList [-i, -(litc x)]
                       , SV.fromList [i, (litc x)]]
    (ELit _)        -> []
    (EConjunct _)   -> SV.fromList (i : (map (negate . litc) cs)) : (map (\c -> SV.fromList [-i, (litc c)]) cs)
    (EDisjunct _)   -> SV.fromList (-i : map litc cs) : (map (\c -> SV.fromList [i, -(litc c)]) cs)
    where
        i       = fromIntegral $ exprIndex e
        cs      = exprChildren (exprType e)
        (x:_)   = cs
        litc (Var Pos v) = fromIntegral v
        litc (Var Neg v) = fromIntegral (-v)
