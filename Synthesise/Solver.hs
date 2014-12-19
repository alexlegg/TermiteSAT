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
    cand <- findCandidate player spec s gt
    liftLog $ logCandidate cand
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
    (fml, copyMap)  <- makeFml spec player s gt
    (dMap, _, d)    <- liftE $ toDimacs Nothing fml
    res             <- liftIO $ satSolve (maximum $ Map.elems dMap) [] d

    if satisfiable res
    then do
        let (Just m)    = model res
        let leaves      = gtLeaves gt
        init            <- getVarsAtRank (svars spec) dMap m 0 (gtBaseRank gt)
        moves           <- mapM (getMove player spec dMap copyMap m) leaves
        let leafMoves = map (gtPlayerMoves player) leaves
        let blah = map (uncurry zip) $ zip leafMoves (map (map (Just . fst)) moves)
        liftIO $ mapM (mapM (\(x, y) -> if x == y || isNothing x then return () else putStrLn (show x ++ " != " ++ show y))) blah
        let paths       = zipWith (fixPlayerMoves player) (map makePathTree leaves) moves
        return (Just (merge (map (fixInitState init) paths)))
    else do
---        mapM_ (learnStates spec player) (gtUnsetNodes gt)
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
    (fml, copyMap)  <- makeFml spec player fakes gt'
    (dMap, a, d)    <- liftE $ toDimacs (Just s) fml

    res <- liftIO $ satSolve (maximum $ Map.elems dMap) a d

    if satisfiable res
    then liftIO $ putStrLn "Invalid Prefix"
    else do
        noAssumps <- liftIO $ satSolve (maximum $ Map.elems dMap) [] d

        if (satisfiable noAssumps)
        then do
            c <- getConflicts (svars spec) dMap (fromJust (conflicts res)) 0 rank
            ls <- get
            liftLog $ logLosingState (printPartialAssignment (vinfo spec) c)
            if null c
            then do
                --This shouldn't really happen, I think the new glucose is to blame
                liftIO $ putStrLn "SAT Solver is not giving us a conflict"
            else do
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
    then return $ map (\(k, a) -> "rank " ++ show k ++ ": " ++ printPartialAssignment (vinfo spec) a) (ungroupZip (Map.toList winningUn))
    else return $ map (printPartialAssignment (vinfo spec)) winningEx

printPartialAssignment :: [VarInfo] -> [Assignment] -> String
printPartialAssignment vinfo as = interMap ", " (printPartialVar vinfo) (groupBy f as)
    where f (Assignment _ x) (Assignment _ y) = varname x == varname y

printPartialVar :: [VarInfo] -> [Assignment] -> String
printPartialVar vinfo as = vname ++ " = " ++ show vals
    where
        vname   = let (Assignment _ v) = (head as) in varname v
        size    = sz (fromJust (find (\v -> name v == vname) vinfo))
        vals    = signsToVals 1 [0] (map f [0..size-1])
        f b     = fmap (flipSign . sign) (find (\(Assignment s v) -> bit v == b) as)

sign (Assignment s _) = s

signsToVals v vs []                   = vs
signsToVals v vs (Nothing: bs)        = signsToVals (v*2) (vs ++ map (+ v) vs) bs
signsToVals v vs ((Just Pos): bs)     = signsToVals (v*2) (map (+ v) vs) bs
signsToVals v vs ((Just Neg): bs)     = signsToVals (v*2) vs bs

verify :: Player -> CompiledSpec -> Expression -> GameTree -> GameTree -> SolverT (Maybe GameTree)
verify player spec s gt cand = do
    let og = projectMoves gt cand
    when (not (isJust og)) $ throwError $ "Error projecting, moves didn't match\n" ++ printTree gt ++ printTree cand
    let leaves = filter ((/= 0) . gtRank) (map makePathTree (gtLeaves (fromJust og)))
    mapMUntilJust (verifyLoop (opponent player) spec s) (zip [0..] leaves)

verifyLoop :: Player -> CompiledSpec -> Expression -> (Int, GameTree) -> SolverT (Maybe GameTree)
verifyLoop player spec s (i, gt) = do
    liftLog $ logVerify i
    let oppGame = appendChild gt
    solveAbstract player spec s oppGame

refine gt cex = do
---    liftIO $ putStrLn "============================="
---    liftIO $ putStrLn $ printTree gt
---    liftIO $ putStrLn $ printTree cex
    let r = appendNextMove gt cex
---    liftIO $ putStrLn $ printTree r
---    liftIO $ putStrLn "============================="
    return r

getMove player spec dMap copyMap model gt = do
    let vars    = if player == Existential then cont spec else ucont spec
    let maxrnk  = gtBaseRank gt
    let copies  = tail $ foldl getCpy [0] (tail (inits (groupCrumb (gtCrumb gt))))
    let rCopies = zip (copies ++ replicate (maxrnk - (length copies)) 0) (reverse [1..maxrnk])
    states      <- mapM (uncurry (getVarsAtRank (svars spec) dMap model)) (map (mapSnd (\r -> r - 1)) rCopies)
    moves       <- mapM (uncurry (getVarsAtRank vars dMap model)) rCopies
    let blah = makePathTree gt
    when (any null moves) $ throwError ("Bad moves\n" ++ show rCopies)
    when (null moves) $ throwError "No Moves"
    return $ zip moves states
    where
        getCpy p crumb = p ++ [fromMaybe (last p) (lookup crumb copyMap)]

getVarsAtRank vars dMap model cpy rnk = do
    let vars' = map (\v -> v {rank = rnk}) vars
    ve <- liftE $ mapM lookupVar vars'
    when (any isNothing ve) $ throwError "Bad expression"
    -- Lookup the dimacs equivalents
    let vd = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vars'
    -- Construct assignments
    when (null vd) $ throwError $ "Bad lookup\n" ++ show rnk ++ show (map (\v -> (cpy, exprIndex v, v)) (catMaybes ve))
    return $ map (makeAssignment . (mapFst (\i -> model !! (i-1)))) vd

getConflicts vars dMap conflicts cpy rnk = do
    let vs  = map (\v -> v {rank = rnk}) vars
    ve      <- liftE $ mapM lookupVar vs
    let vd  = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vs
    let cs  = map (\c -> (abs c, c)) conflicts
    let as  = map ((uncurry liftMFst) . mapFst (\i -> lookup i cs)) vd
    return  $ map makeAssignment (catMaybes as)

