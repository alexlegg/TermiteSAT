{-# LANGUAGE RecordWildCards #-}
module Synthesise.Solver (
      checkRank
    , checkStrategy
    , LearnedStates(..)
    , emptyLearnedStates
    ) where

import Data.Maybe
import Data.List
import Data.Tree
import Data.Tuple.Update
import Data.Foldable (foldlM)
import System.IO
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace

import Expression.Compile
import Expression.Expression
import Expression.AST
import Synthesise.SolverT
import Synthesise.GameTree
import Synthesise.Strategy
import Synthesise.GameFormula
import SatSolver.SatSolver
import SatSolver.Interpolator
import Utils.Logger
import Utils.Utils

checkRank :: CompiledSpec -> Int -> Expression -> SolverT Bool
checkRank spec rnk s = do
    testInterpolants
    r <- solveAbstract Universal spec s (gtNew Existential rnk)
    liftE $ analyseManagers
    return (isNothing r)

testInterpolants :: SolverT ()
testInterpolants = do
    v1  <- liftE $ literal $ ExprVar "testInterp1" StateVar 0 0 0
    v2  <- liftE $ literal $ ExprVar "testInterp2" StateVar 0 0 0
    v3  <- liftE $ literal $ ExprVar "testInterp3" StateVar 0 0 0

    a   <- liftE $ conjunct [v1, v2]
    b'  <- liftE $ implicate v2 v3
    nv3 <- liftE $ negation v3
    b   <- liftE $ conjunct [b', nv3]

    lift $ interpolate 0 a b

    return ()

checkStrategy :: CompiledSpec -> Int -> Expression -> String -> Tree [[Assignment]] -> SolverT Bool
checkStrategy spec rnk s player strat = do
    let p       = if player == "universal" then Universal else Existential
    let gt      = buildStratGameTree p (gtNew Existential rnk) strat
    r           <- solveAbstract Universal spec s gt
    liftIO $ putStrLn "Playing Strategy from file:"
    liftIO $ putStrLn (printTree spec gt)
    return (isNothing r)

buildStratGameTree player gt strat = gtParent $ gtParent $ foldl (buildStratGameTree player) gt' (subForest strat)
    where
        append  = if player == Existential then gtAppendMove else gtAppendMoveU
        gt'     = append gt (Just (concat (rootLabel strat)))

solveAbstract :: Player -> CompiledSpec -> Expression -> GameTree -> SolverT (Maybe GameTree)
solveAbstract player spec s gt = do
---    liftIO $ putStrLn ("Solve abstract for " ++ show player)
---    pLearn <- printLearnedStates spec player
    liftLog $ logSolve gt player []

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
    (es, f, gt')    <- makeFml spec player s gt
    res             <- satSolve gt' Nothing f

    if satisfiable res
    then do
        (Just m)    <- shortenStrategy player gt' f (model res) es
        gt'         <- setMoves player spec m (gtRoot gt')
        return (Just gt')
    else do
        mapM_ (learnStates spec player) (gtUnsetNodes gt)
---        computeCounterExample spec player gt
        return Nothing

learnStates :: CompiledSpec -> Player -> GameTree -> SolverT ()
learnStates spec player ogt = do
    let gt'         = gtRebase ogt
    let (Just as)   = gtPrevState ogt
    let rank        = gtBaseRank gt'
    let s           = map (\x -> setAssignmentRankCopy x rank 0) as

    fakes           <- liftE $ trueExpr
    (es, f, gt)     <- makeFml spec player fakes gt'
    core            <- minimiseCore gt (Just s) f

    when (isJust core) $ do
        c <- getConflicts (svars spec) (fromJust core) 0 rank

        ls <- get
        if player == Existential
        then do
            put $ ls { winningUn = Map.alter (\x -> Just (Set.insert c (fromMaybe Set.empty x))) rank (winningUn ls) }
            liftLog $ logLosingState (printMove spec (Just c))
        else do
            put $ ls { winningEx = winningEx ls ++ [c] }
            liftLog $ logLosingState (printMove spec (Just c))

printLearnedStates spec player = do
    LearnedStates{..} <- get
    if player == Existential
    then do
        return $ map (\(k, e) -> printMove spec (Just e)) (ungroupZip (map (mapSnd Set.toList) (Map.toList winningUn)))
    else do
        return $ map (printMove spec . Just) winningEx

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

setMoves player spec model gt = do
    let f       = if player == gtFirstPlayer gt then setMovesPlayer else setMovesOpp 
    cs          <- mapM (f player spec model) (gtChildren gt)
    let gt'     = gtSetChildren gt cs
    init        <- getVarsAtRank (svars spec) model 0 (gtBaseRank gt)
    return      $ gtSetInit init gt'

setMovesPlayer player spec model gt = do
    let vars    = if player == Existential then cont spec else ucont spec
    move        <- getVarsAtRank vars model (gtCopyId gt) (gtRank gt)

    gt'         <- case player of
        Universal   -> do
            state <- getVarsAtRank (svars spec) model (gtCopyId gt) (gtRank gt - 1)
            return $ gtSetMove (gtSetState gt state) move
        Existential -> 
            return $ gtSetMove gt move

    cs          <- mapM (setMovesOpp player spec model) (gtChildren gt')
    return      $ gtSetChildren gt' cs

setMovesOpp player spec model gt = do
    gt' <- if opponent player == Universal
        then do
            state <- getVarsAtRank (svars spec) model (gtCopyId (gtParent gt)) (gtRank gt - 1)
            return $ gtSetState gt state
        else return gt
    let vars    = if opponent player == Existential then cont spec else ucont spec
    move        <- getVarsAtRank vars model (gtCopyId gt) (gtRank gt)
    let gtm     = gtMove gt
    cs          <- mapM (setMovesPlayer player spec model) (gtChildren gt')
    return      $ gtSetChildren gt' cs

eqMoves xs ys = all id $ map (uncurry eqAssignments) $ zip xs ys
    where
    eqAssignments (Assignment s1 v1) (Assignment s2 v2) = s1 == s2 && eqVars v1 v2
    eqVars v1 v2 = v1 {ecopy = 0} == v2 {ecopy = 0}

getVarsAtRank vars model cpy rnk = do
    let vars' = map (\v -> v {rank = rnk, ecopy = cpy}) vars
    ve <- liftE $ mapM lookupVar vars'
    when (any isNothing ve) $ throwError ("Bad expression:\n" ++ interMap "\n" show (zip vars' ve))
    -- Lookup the dimacs equivalents
    let vd = zip (map exprIndex (catMaybes ve)) vars'
    -- Construct assignments
    when (null vd) $ throwError $ "Bad lookup " ++ show cpy ++ " " ++ show rnk
    return $ map (makeAssignment . (mapFst (\i -> model !! (i-1)))) vd

getConflicts vars conflicts cpy rnk = do
    let vs  = map (\v -> v {rank = rnk, ecopy = cpy}) vars
    ve      <- liftE $ mapM lookupVar vs
    let vd  = zip (map exprIndex (catMaybes ve)) vs
    let cs  = map (\c -> (abs c, c)) conflicts
    let as  = map ((uncurry liftMFst) . mapFst (\i -> lookup i cs)) vd
    return  $ map makeAssignment (catMaybes as)

shortenStrategy :: Player -> GameTree -> Expression -> Maybe [Int] -> [[Expression]] -> SolverT (Maybe [Int])
shortenStrategy Existential gt fml model es = do
    let reversedEs  = map reverse es
    (_, m')         <- foldlM (shortenLeaf gt) (fml, model) reversedEs
    return m'
shortenStrategy _ _ _ m _ = return m

shortenLeaf gt (fml, m) (e:es) = do
    let maxCopy = gtMaxCopy gt
    ne          <- liftE $ negationTemp maxCopy e
    fml'        <- liftE $ conjunctTemp maxCopy [fml, ne]
    res         <- satSolve gt Nothing fml'
    if satisfiable res
    then do
        shortenLeaf gt (fml', model res) es
    else do
        return (fml, m)
shortenLeaf _ (fml, m) [] = return (fml, m)
