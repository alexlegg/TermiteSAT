{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
        synthesise
      , unboundedSynthesis
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops
import Data.Maybe
import qualified Data.Set as Set
import Data.List.Split
import System.IO
import System.CPUTime
import Text.Printf

import Utils.Logger
import Utils.Utils
import Expression.Parse
import Expression.Compile
import Expression.Expression
import Synthesise.Solver
import Synthesise.SolverT
import Synthesise.Config
import Expression.AST

synthesise :: Int -> ParsedSpec -> Config -> EitherT String (LoggerT IO) (Maybe Int)
synthesise k spec def = do
    evalStateT (synthesise' k spec def BoundedLearning) emptyManager

unboundedSynthesis :: ParsedSpec -> Config -> EitherT String (LoggerT IO) (Maybe Int)
unboundedSynthesis spec config = do
    evalStateT (unbounded spec config) emptyManager

unbounded :: ParsedSpec -> Config -> ExpressionT (LoggerT IO) (Maybe Int)
unbounded spec config = do
    (i, cspec) <- loadFmls 1 spec
    defMoves <- case (moveLearning config) of
        MLFixedMoves fn -> do
            (uMoves, eMoves) <- readMovesFile fn
            uVars <- mapM (mapM (mapFstM lookupVarName)) uMoves
            let uAss = map (concat . (map (\(var, val) -> makeAssignmentValue var val))) uVars
            eVars <- mapM (mapM (mapFstM lookupVarName)) eMoves
            let eAss = map (concat . (map (\(var, val) -> makeAssignmentValue var val))) eVars
            return $ Just (uAss, eAss)
        _ -> return Nothing
    evalStateT (unboundedLoop i cspec defMoves config 0 1) (emptyLearnedStates UnboundedLearning)

unboundedLoop :: [Assignment] -> CompiledSpec -> Maybe ([[Assignment]], [[Assignment]]) -> Config -> Int -> Int -> SolverT (Maybe Int)
unboundedLoop i spec def config satcalls k = do
    liftIO $ putStrLn "-----"
    liftIO $ putStrLn $ "Unbounded Loop " ++ show k
    liftIO $ hPutStrLn stderr $ "Unbounded Loop " ++ show k

    ls <- get 

    exWins <- checkInit k i (map Set.toList (Set.toList (winningMust ls))) (head (cg spec))

    unWins <- checkUniversalWin k

    if exWins
    then finishedLoop (Just (k-1)) satcalls
    else do
        if unWins
        then finishedLoop Nothing satcalls
        else do
            t1      <- liftIO $ getCPUTime
            (sc, r) <- checkRank spec k i def config
            t2      <- liftIO $ getCPUTime
            let t   = fromIntegral (t2-t1) * 1e-12 :: Double

            liftIO $ printf "checkRank : %6.2fs\n" t

            if r
            then finishedLoop (Just k) (sc + satcalls) --Counterexample exists for Universal player
            else do
                spec' <- liftE $ unrollSpec spec
                let init' = map (\a -> setAssignmentRankCopy a (k+1) 0) i 
                unboundedLoop init' spec' def config (satcalls + sc) (k+1)

finishedLoop :: Maybe Int -> Int -> SolverT (Maybe Int)
finishedLoop r satcalls = do
    liftIO $ putStrLn $ "Total SAT Calls: " ++ (show satcalls)
    return r

synthesise' :: Int -> ParsedSpec -> Config -> LearningType -> ExpressionT (LoggerT IO) (Maybe Int)
synthesise' k spec config learning = do
    (i, cspec) <- loadFmls k spec
    defMoves <- case (moveLearning config) of
        MLFixedMoves fn -> do
            (uMoves, eMoves) <- readMovesFile fn
            uVars <- mapM (mapM (mapFstM lookupVarName)) uMoves
            let uAss = map (concat . (map (\(var, val) -> makeAssignmentValue var val))) uVars
            eVars <- mapM (mapM (mapFstM lookupVarName)) eMoves
            let eAss = map (concat . (map (\(var, val) -> makeAssignmentValue var val))) eVars
            return $ Just (uAss, eAss)
        _ -> return Nothing
    (_, r) <- evalStateT (checkRank cspec k i defMoves config) (emptyLearnedStates learning)
    return $ if r then (Just k) else Nothing

enumValidity :: MonadIO m => VarInfo -> ExpressionT m (Maybe Expression)
enumValidity (VarInfo {enum = Nothing})     = return Nothing
enumValidity vi@(VarInfo {enum = Just es})  = do
    let invalid = [(length es)..((2 ^ sz vi)-1)]
    if null invalid
    then return Nothing
    else do 
        eqs <- mapM ((negation =<<) . equalsConstant (compileVar vi)) invalid
        c   <- conjunct eqs
        c'  <- setRank 1 c
        return (Just c')

loadFmls :: Int -> ParsedSpec -> ExpressionT (LoggerT IO) ([Assignment], CompiledSpec)
loadFmls k spec = do
    let ParsedSpec{..} = spec

    when (null trans) $ lift $ left "Empty transition relation"

    t' <- if isJust aigTrans
        then compileAIG (fromJust aigTrans) (fromJust aigVars)
        else mapM compile trans

    t   <- conjunct t'
    g'  <- compile goal
    cg  <- setRank 0 g'
    ug  <- negation cg
    u   <- mapM compile ucont

    let svars = concatMap compileVar stateVars
    let uvars = concatMap compileVar ucontVars
    let cvars = concatMap compileVar contVars

    let vinfo = stateVars ++ ucontVars ++ contVars

    vus <- if isJust ucont
        then do
            u_idle  <- equalsConstant (map (\v -> v {rank = 1}) uvars) 0
            uev     <- mapM enumValidity ucontVars
            vu'     <- implicate (fromJust u) =<< (negation u_idle)
            vu      <- conjunct (vu' : catMaybes uev)
            iterateNM (k-1) unrollExpression vu
        else return []

    vcs <- if isJust ucont
        then do
            c_idle  <- equalsConstant (map (\v -> v {rank = 1}) cvars) 0
            vc      <- equate c_idle (fromJust u)
            iterateNM (k-1) unrollExpression vc
        else return []

    ts  <- iterateNM (k-1) unrollExpression t
    cgs <- iterateNM k unrollExpression cg
    ugs <- iterateNM k unrollExpression ug

    us  <- if isJust ucont
        then iterateNM (k-1) unrollExpression (fromJust u)
        else return []

    steps <- if isJust ucont
        then zipWith3M (\s vc vu -> conjunct [s, vc, vu]) ts vcs vus
        else return ts

    let cspec = CompiledSpec {
          t         = steps
        , useFair   = isJust ucont
        , cg        = cgs
        , ug        = ugs
        , u         = us
        , vc        = vcs
        , vu        = vus
        , cont      = cvars
        , ucont     = uvars
        , svars     = svars
        , vinfo     = vinfo
        }

    lift $ lift $ logSpec cspec

    let initAssignments = map (\a -> setAssignmentRankCopy a k 0) (compileInit initial)

    initManager
    return (initAssignments, cspec)

unrollSpec :: MonadIO m => CompiledSpec -> ExpressionT m CompiledSpec
unrollSpec spec = do
    
    t'  <- unrollExpression (last (t spec))
    cg' <- unrollExpression (last (cg spec))
    ug' <- unrollExpression (last (ug spec))

    spec' <- if (useFair spec)
        then do
            u'  <- unrollExpression (last (u spec))
            vc' <- unrollExpression (last (vc spec))
            vu' <- unrollExpression (last (vu spec))

            return spec {
                  t   = t spec ++ [t']
                , cg  = cg spec ++ [cg']
                , ug  = ug spec ++ [ug']
                , u   = u spec ++ [u']
                , vc  = vc spec ++ [vc']
                , vu  = vu spec ++ [vu']
            }
        else do
            return spec {
                  t   = t spec ++ [t']
                , cg  = cg spec ++ [cg']
                , ug  = ug spec ++ [ug']
            }

    initManager
    return spec'

iterateNM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateNM 0 _ x = return [x]
iterateNM n f x = do
    fx <- f x
    xs <- iterateNM (n - 1) f fx
    return (x : xs)

readValue :: String -> (String, Int)
readValue s = let [l, r] = splitOn " = " s in (l, read r :: Int)

readMovesFile :: MonadIO m => FilePath -> m ([[([Char], Int)]], [[([Char], Int)]])
readMovesFile fn = do
    liftIO $ withFile fn ReadMode $ \h -> do
        uMoves <- unfoldM (readMove h)
        eMoves <- unfoldM (readMove h)
        return (uMoves, eMoves)

readMove :: Handle -> IO (Maybe [([Char], Int)])
readMove h = do
    eof <- hIsEOF h
    if eof
    then return Nothing
    else do
        line <- hGetLine h
        return $ case line of
            ""      -> Nothing
            _       -> Just $ map readValue $ splitOn ", " line

