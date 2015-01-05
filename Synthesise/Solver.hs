{-# LANGUAGE RecordWildCards #-}
module Synthesise.Solver (
      checkRank
    , LearnedStates(..)
    , emptyLearnedStates
    ) where

import Data.Maybe
import Data.List
import Data.Tuple.Update
import System.IO
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops
import qualified Data.Map as Map

import Expression.Compile
import Expression.Expression
import Expression.AST
import Synthesise.SolverT
import Synthesise.GameTree
import Synthesise.Strategy
import Synthesise.GameFormula
import SatSolver.SatSolver
import Utils.Logger
import Utils.Utils

checkRank :: CompiledSpec -> Int -> Expression -> SolverT Bool
checkRank spec rnk s = do
    r <- solveAbstract Universal spec s (gtNew Existential rnk)
    return (isNothing r)

solveAbstract :: Player -> CompiledSpec -> Expression -> GameTree -> SolverT (Maybe GameTree)
solveAbstract player spec s gt = do
---    liftIO $ putStrLn ("Solve abstract for " ++ show player)
    pLearn <- printLearnedStates spec player
    liftLog $ logSolve gt player pLearn

    liftE $ pushCache

    cand <- findCandidate player spec s gt
    liftLog $ logCandidate cand

    liftE $ popCache

    res <- refinementLoop player spec s cand gt gt

    liftLog $ logSolveComplete res
    liftLog logDumpLog

    return res

refinementLoop :: Player -> CompiledSpec -> Expression -> Maybe GameTree -> GameTree -> GameTree -> SolverT (Maybe GameTree)
refinementLoop player spec s Nothing origGT absGt = do
---    liftIO $ putStrLn ("Could not find a candidate for " ++ show player)
    return Nothing
refinementLoop player spec s (Just cand) origGT absGT = do
    v <- verify player spec s origGT cand
    case v of
        (Just cex) -> do
---            liftIO $ putStrLn ("Counterexample found against " ++ show player)
            absGT' <- refine absGT cex
            liftLog $ logRefine
            cand' <- solveAbstract player spec s absGT'
            refinementLoop player spec s cand' origGT absGT'
        Nothing -> do
---            liftIO $ putStrLn ("Verified candidate for " ++ show player)
            return (Just cand)
    

findCandidate :: Player -> CompiledSpec -> Expression -> GameTree -> SolverT (Maybe GameTree)
findCandidate player spec s gt = do
    fml             <- makeFml spec player s gt
    (dMap, _, d)    <- liftE $ toDimacs Nothing fml
    res             <- liftIO $ satSolve (maximum $ Map.elems dMap) [] d

    if satisfiable res
    then do
        let (Just m)    = model res
        gt'             <- setMoves player spec dMap m (gtRoot gt)
        return (Just gt')
    else do
        mapM_ (learnStates spec player) (gtUnsetNodes gt)
---        computeCounterExample spec player gt
        return Nothing

learnStates :: CompiledSpec -> Player -> GameTree -> SolverT ()
learnStates spec player gt = do
    let gt'         = gtRebase gt
    let (Just s)    = gtPrevState gt
    let rank        = gtBaseRank gt'

    fakes           <- liftE $ trueExpr
    fml             <- makeFml spec player fakes gt'
    (dMap, a, d)    <- liftE $ toDimacs (Just s) fml

    res <- liftIO $ satSolve (maximum $ Map.elems dMap) a d

    when (unsatisfiable res) $ do
        noAssumps <- liftIO $ satSolve (maximum $ Map.elems dMap) [] d

        if (satisfiable noAssumps)
        then do
            core <- liftIO $ minimiseCore (maximum $ Map.elems dMap) (fromJust (conflicts res)) d
            c <- getConflicts (svars spec) dMap core 0 rank

            ls <- get
            if player == Existential
            then do
                put $ ls { winningUn = Map.alter (\x -> Just (fromMaybe [] x ++ [c])) rank (winningUn ls) }
                liftLog $ logLosingState (printMove spec (Just c))
            else do
                put $ ls { winningEx = winningEx ls ++ [c] }
                liftLog $ logLosingState (printMove spec (Just c))
        else do
            -- Player loses for all states here
            -- TODO Learn something
            liftIO $ putStrLn $ "Lose all states"
            return ()

printLearnedStates spec player = do
    LearnedStates{..} <- get
    if player == Existential
    then return $ map (\(k, a) -> "rank " ++ show k ++ ": " ++ printMove spec (Just a)) (ungroupZip (Map.toList winningUn))
    else return $ map (printMove spec . Just) winningEx

verify :: Player -> CompiledSpec -> Expression -> GameTree -> GameTree -> SolverT (Maybe GameTree)
verify player spec s gt cand = do
    let og = projectMoves gt cand
    when (not (isJust og)) $ throwError $ "Error projecting, moves didn't match\n" ++ show player ++ printTree spec gt ++ printTree spec cand
    let leaves = filter (not . gtAtBottom) (map makePathTree (gtLeaves (fromJust og)))
    mapMUntilJust (verifyLoop (opponent player) spec s) (zip [0..] leaves)

verifyLoop :: Player -> CompiledSpec -> Expression -> (Int, GameTree) -> SolverT (Maybe GameTree)
verifyLoop player spec s (i, gt) = do
    liftLog $ logVerify i
    let oppGame = appendChild gt
    solveAbstract player spec s oppGame

refine gt cex = return $ appendNextMove gt cex

setMoves player spec dMap model gt = do
    let f       = if player == gtFirstPlayer gt then setMovesPlayer else setMovesOpp 
    cs          <- mapM (f player spec dMap model) (gtChildren gt)
    let gt'     = gtSetChildren gt cs
    init        <- getVarsAtRank (svars spec) dMap model 0 (gtBaseRank gt)
    return      $ gtSetInit init gt'

setMovesPlayer player spec dMap model gt = do
    let vars    = if player == Existential then cont spec else ucont spec
    move        <- getVarsAtRank vars dMap model (gtCopyId gt) (gtRank gt)
    gt'         <- if player == Universal
        then do
            state <- getVarsAtRank (svars spec) dMap model (gtCopyId gt) (gtRank gt - 1)
            return $ gtSetMove (gtSetState gt state) move
        else return $ gtSetMove gt move
    cs          <- mapM (setMovesOpp player spec dMap model) (gtChildren gt')
    return      $ gtSetChildren gt' cs

setMovesOpp player spec dMap model gt = do
    gt' <- if opponent player == Universal
        then do
            state <- getVarsAtRank (svars spec) dMap model (gtCopyId gt) (gtRank gt - 1)
            return $ gtSetState gt state
        else return gt
    cs          <- mapM (setMovesPlayer player spec dMap model) (gtChildren gt')
    return      $ gtSetChildren gt' cs

getVarsAtRank vars dMap model cpy rnk = do
    let vars' = map (\v -> v {rank = rnk, ecopy = cpy}) vars
    ve <- liftE $ mapM lookupVar vars'
    when (any isNothing ve) $ throwError "Bad expression"
    -- Lookup the dimacs equivalents
    let vd = zipMaybe1 (map (\v -> Map.lookup (0, exprIndex v) dMap) (catMaybes ve)) vars'
    -- Construct assignments
    when (null vd) $ throwError $ "Bad lookup " ++ show cpy ++ " " ++ show rnk
    return $ map (makeAssignment . (mapFst (\i -> model !! (i-1)))) vd

getConflicts vars dMap conflicts cpy rnk = do
    let vs  = map (\v -> v {rank = rnk}) vars
    ve      <- liftE $ mapM lookupVar vs
    let vd  = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vs
    let cs  = map (\c -> (abs c, c)) conflicts
    let as  = map ((uncurry liftMFst) . mapFst (\i -> lookup i cs)) vd
    return  $ map makeAssignment (catMaybes as)

