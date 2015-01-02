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
---    liftLog logDumpLog

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
        let leaves      = gtLeaves gt'

        moves           <- mapM (getMove player spec dMap m) leaves

        let paths       = zipWith (fixPlayerMoves player) (map makePathTree leaves) moves

        return (Just (merge paths))
    else do
        mapM_ (learnStates spec player) (gtUnsetNodes gt)
---        computeCounterExample spec player gt
        return Nothing

merge (t:[]) = t
merge (t:ts) = foldl mergeTrees t ts

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
            then put $ ls { winningUn = Map.alter (\x -> Just (fromMaybe [] x ++ [c])) rank (winningUn ls) }
            else put $ ls { winningEx = winningEx ls ++ [c] }
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
    liftIO $ putStrLn "setMoves"
    cs          <- mapM (f player spec dMap model) (gtChildren gt)
    let gt'     = gtSetChildren gt cs
    liftIO $ putStrLn $ printTree spec gt
    liftIO $ putStrLn $ printTree spec gt'
    liftIO $ putStrLn "get init"
    init        <- getVarsAtRank (svars spec) dMap model 0 (gtBaseRank gt)
    liftIO $ putStrLn "get init done"
    return      $ fixInitState init gt'

setMovesPlayer player spec dMap model gt = do
    let vars    = if player == Existential then cont spec else ucont spec
    let copy    = gtCopyId gt
    let rnk     = gtRank gt
    move        <- getVarsAtRank vars dMap model copy rnk
    liftIO $ putStrLn (printMove spec (Just move))
    let gt'     = gtSetMove gt move
    cs          <- mapM (setMovesOpp player spec dMap model) (gtChildren gt')
    liftIO $ putStrLn $ "setMove player " ++ show (length (gtChildren gt)) ++ " " ++ show (length (gtChildren gt')) ++ " " ++ show (length cs)
    return      $ gtSetChildren gt' cs

setMovesOpp player spec dMap model gt = do
    liftIO $ putStrLn "setMove opp"
    cs          <- mapM (setMovesPlayer player spec dMap model) (gtChildren gt)
    liftIO $ putStrLn $ "setMove player " ++ show (length (gtChildren gt)) ++ " " ++ show (length cs)
    return      $ gtSetChildren gt cs

getMove player spec dMap model gt = do
    let vars    = if player == Existential then cont spec else ucont spec
    let maxrnk  = gtBaseRank gt
    let copies = if player == gtFirstPlayer gt
                    then everyOdd (tail (gtCopies gt))
                    else everyEven (tail (gtCopies gt))
    let scopies = everyEven (tail (gtCopies gt))
    states      <- zipWithM (getVarsAtRank (svars spec) dMap model) scopies (reverse [0..(maxrnk-1)])
    moves       <- zipWithM (getVarsAtRank vars dMap model) copies (reverse [1..maxrnk])
    when (any null moves) $ throwError "Bad moves"
    when (null moves) $ throwError "No Moves"
    return $ zip moves states

getVarsAtRank vars dMap model cpy rnk = do
    let vars' = map (\v -> v {rank = rnk}) vars
    ve <- liftE $ mapM lookupVar vars'
    when (any isNothing ve) $ throwError "Bad expression"
    -- Lookup the dimacs equivalents
    let vd = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vars'
    -- Construct assignments
    when (null vd) $ throwError $ "Bad lookup " ++ show (cpy, rnk) ++ "\n" ++ show (map (\v -> (cpy, exprIndex v, v)) (catMaybes ve))
    return $ map (makeAssignment . (mapFst (\i -> model !! (i-1)))) vd

getConflicts vars dMap conflicts cpy rnk = do
    let vs  = map (\v -> v {rank = rnk}) vars
    ve      <- liftE $ mapM lookupVar vs
    let vd  = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vs
    let cs  = map (\c -> (abs c, c)) conflicts
    let as  = map ((uncurry liftMFst) . mapFst (\i -> lookup i cs)) vd
    return  $ map makeAssignment (catMaybes as)

