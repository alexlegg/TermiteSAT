{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
        synthesise
      , unboundedSynthesis
      , playStrategy
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops
import Data.Functor
import Data.Maybe
import Data.Tree
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Data.List
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
import Synthesise.GameTree
import Synthesise.Config
import Expression.AST
import SatSolver.Interpolator

synthesise :: Int -> ParsedSpec -> Config -> EitherT String (LoggerT IO) (Maybe Int)
synthesise k spec def = do
    evalStateT (synthesise' k spec def BoundedLearning) emptyManager

unboundedSynthesis :: ParsedSpec -> Config -> EitherT String (LoggerT IO) (Maybe Int)
unboundedSynthesis spec config = do
    evalStateT (unbounded spec config) emptyManager

unbounded spec config = do
    (init, cspec) <- loadFmls 1 spec
    defMoves <- case (moveLearning config) of
        MLFixedMoves fn -> do
            (uMoves, eMoves) <- readMovesFile fn
            uVars <- mapM (mapM (mapFstM lookupVarName)) uMoves
            let uAss = map (concat . (map (\(var, val) -> makeAssignmentValue var val))) uVars
            eVars <- mapM (mapM (mapFstM lookupVarName)) eMoves
            let eAss = map (concat . (map (\(var, val) -> makeAssignmentValue var val))) eVars
            return $ Just (uAss, eAss)
        _ -> return Nothing
    evalStateT (unboundedLoop init cspec defMoves config 0 1) (emptyLearnedStates UnboundedLearning)

unboundedLoop :: [Assignment] -> CompiledSpec -> Maybe ([[Assignment]], [[Assignment]]) -> Config -> Int -> Int -> SolverT (Maybe Int)
unboundedLoop init spec def config satcalls k = do
    liftIO $ putStrLn "-----"
    liftIO $ putStrLn $ "Unbounded Loop " ++ show k
    liftIO $ hPutStrLn stderr $ "Unbounded Loop " ++ show k

    ls <- get 

---    liftIO $ withFile ("debug/winningMay" ++ show (k-1)) WriteMode $ \h -> do
---        forM (Map.toList (winningMay ls)) $ \(r, wm) -> do
---            hPutStrLn h (show r)
---            forM (Set.toList wm) $ \s ->
---                hPutStrLn h (printMove spec (Just (sort (Set.toList s))))
---            hPutStrLn h "--"
---        return ()

---    liftIO $ withFile ("debug/winningMust" ++ show (k-1)) WriteMode $ \h -> do
---        forM (Set.toList (winningMust ls)) $ \s ->
---            hPutStrLn h (printMove spec (Just (sort (Set.toList s))))

    exWins <- checkInit k init (map Set.toList (Set.toList (winningMust ls))) (head (cg spec))

    unWins <- checkUniversalWin spec k

    if exWins
    then finishedLoop spec (Just (k-1)) satcalls
    else do
        if unWins
        then finishedLoop spec Nothing satcalls
        else do
            t1      <- liftIO $ getCPUTime
            (sc, r) <- checkRank spec k init def config
            t2      <- liftIO $ getCPUTime
            let t   = fromIntegral (t2-t1) * 1e-12 :: Double

            liftIO $ printf "checkRank : %6.2fs\n" t

            if r
            then finishedLoop spec (Just k) (sc + satcalls) --Counterexample exists for Universal player
            else do
                spec' <- liftE $ unrollSpec spec
                let init' = map (\a -> setAssignmentRankCopy a (k+1) 0) init
                unboundedLoop init' spec' def config (satcalls + sc) (k+1)

finishedLoop :: CompiledSpec -> Maybe Int -> Int -> SolverT (Maybe Int)
finishedLoop spec r satcalls = do
    ls <- get
    liftIO $ putStrLn $ "Total SAT Calls: " ++ (show satcalls)
    return r

synthesise' k spec config learning = do
    (init, cspec) <- loadFmls k spec
    defMoves <- case (moveLearning config) of
        MLFixedMoves fn -> do
            (uMoves, eMoves) <- readMovesFile fn
            uVars <- mapM (mapM (mapFstM lookupVarName)) uMoves
            let uAss = map (concat . (map (\(var, val) -> makeAssignmentValue var val))) uVars
            eVars <- mapM (mapM (mapFstM lookupVarName)) eMoves
            let eAss = map (concat . (map (\(var, val) -> makeAssignmentValue var val))) eVars
            return $ Just (uAss, eAss)
        _ -> return Nothing
    (sc, r) <- evalStateT (checkRank cspec k init defMoves config) (emptyLearnedStates learning)
    return $ if r then (Just k) else Nothing

playStrategy :: Int -> ParsedSpec -> Config -> FilePath -> EitherT String (LoggerT IO) (Maybe Int)
playStrategy k spec config sFile = evalStateT (playStrategy' k spec config sFile) emptyManager

playStrategy' k spec config sFile = do
    (player, strat) <- readStrategyFile k sFile
    (init, cspec)   <- loadFmls k spec
    vars            <- mapM (mapFstM (mapM (mapFstM lookupVarName))) strat
    let varTree     = unfoldTree makeStrategy vars
    let assTree     = fmap (\(vs, r) -> map (\(var, val) -> makeAssignmentValue (map (setVarRank (r+1)) var) val) vs) varTree

    r <- evalStateT (checkStrategy cspec config k init player assTree) (emptyLearnedStates BoundedLearning)
    return $ if r then (Just k) else Nothing

makeStrategy :: [(a, Int)] -> ((a, Int), [[(a, Int)]])
makeStrategy ((x, r):xrs) = ((x, r), children xrs)
    where
        children []                 = []
        children ((x', r'):xrs')    = if r' == r-1
                                    then let (cs, ncs) = span (\(a, b) -> b < r-1) xrs' in
                                        ((x', r') : cs) : children ncs
                                    else []

enumValidity vi@(VarInfo {enum = Nothing}) = return Nothing
enumValidity vi@(VarInfo {enum = Just es}) = do
    let vars = compileVar vi
    let invalid = [(length es)..((2 ^ sz vi)-1)]
    if null invalid
    then return Nothing
    else do 
        eqs <- mapM ((negation =<<) . equalsConstant vars) invalid
        c <- conjunct eqs
        c' <- setRank 1 c
        return (Just c')

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
        then zipWith3M (\t vc vu -> conjunct [t, vc, vu]) ts vcs vus
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

    let initAssignments = map (\a -> setAssignmentRankCopy a k 0) (compileInit init)

    initManager (map exprIndex (steps ++ cgs ++ ugs ++ us ++ vcs ++ vus))
    return (initAssignments, cspec)

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

    initManager (map exprIndex ((t spec') ++ (cg spec') ++ (ug spec') ++ (u spec') ++ (vc spec') ++ (vu spec')))
    return spec'

iterateNM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateNM 0 f x = return [x]
iterateNM n f x = do
    fx <- f x
    xs <- iterateNM (n - 1) f fx
    return (x : xs)

readStrategyFile k fn = do
    liftIO $ withFile fn ReadMode $ \h -> do
        player <- hGetLine h
        strategy <- whileM (fmap not $ hIsEOF h) $ do
            line <- hGetLine h
            let depth   = length (takeWhile (== ' ') line) `div` 4
            let nvPairs = map readValue $ splitOn ", " (dropWhile (== ' ') line)
            return (nvPairs, k-(depth+1))
        return (player, strategy)

readValue s = let [l, r] = splitOn " = " s in (l, read r :: Int)

readMovesFile fn = do
    liftIO $ withFile fn ReadMode $ \h -> do
        uMoves <- unfoldM (readMove h)
        eMoves <- unfoldM (readMove h)
        return (uMoves, eMoves)

readMove h = do
    eof <- hIsEOF h
    if eof
    then return Nothing
    else do
        line <- hGetLine h
        return $ case line of
            ""      -> Nothing
            _       -> Just $ map readValue $ splitOn ", " line

