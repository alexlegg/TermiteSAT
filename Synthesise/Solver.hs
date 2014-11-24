{-# LANGUAGE RecordWildCards #-}
module Synthesise.Solver (
    checkRank
    ) where

import Data.Maybe
import Data.List
import Data.Tuple.Update
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops
import qualified Data.Map as Map

import Expression.Compile
import Expression.Expression
import Synthesise.GameTree
import SatSolver.SatSolver
import Utils.Logger
import Utils.Utils

checkRank :: CompiledSpec -> Int -> Expression -> ExpressionT (LoggerT IO) Bool
checkRank spec rnk s = do
    r <- solveAbstract Existential spec s (gtNew Existential rnk)
    return (isJust r)

solveAbstract :: Player -> CompiledSpec -> Expression -> GameTree -> ExpressionT (LoggerT IO) (Maybe GameTree)
solveAbstract player spec s gt = do
    liftIO $ putStrLn ("Solve abstract for " ++ show player)
---    liftIO $ putStrLn (printTree gt)
    cand <- findCandidate player spec s gt
    lift $ lift $ logSolve gt cand player
    res <- refinementLoop player spec s cand gt gt
    lift $ lift $ logSolveComplete res
    return res

refinementLoop :: Player -> CompiledSpec -> Expression -> Maybe GameTree -> GameTree -> GameTree -> ExpressionT (LoggerT IO) (Maybe GameTree)
refinementLoop player spec s cand origGT absGT = do
    if isJust cand
    then do
        cex <- verify player spec s origGT (fromJust cand)

        if isJust cex
            then do
---                liftIO $ putStrLn ("Counterexample found against " ++ show player)
                absGT' <- refine player absGT (fromJust cex)
                lift $ lift $ logRefine
                cand' <- solveAbstract player spec s absGT'
                refinementLoop player spec s cand' origGT absGT'
            else do
---                liftIO $ putStrLn ("Verified candidate for " ++ show player)
                return cand
    else do
---        liftIO $ putStrLn ("Could not find a candidate for " ++ show player)
        return Nothing
    

findCandidate :: Player -> CompiledSpec -> Expression -> GameTree -> ExpressionT (LoggerT IO) (Maybe GameTree)
findCandidate player spec s gt = do
    let CompiledSpec{..} = spec

    (copyMap, fml) <- if player == Existential
         then driverFml spec player s gt
         else environmentFml spec player s gt

    (dMap, dimacs) <- toDimacs fml
---    fp <- printExpression fml
---    liftIO $ putStrLn fp
---    liftIO $ putStrLn (interMap "\n" (interMap " " show) dimacs)
    res <- liftIO $ satSolve (maximum $ Map.elems dMap) dimacs
---    liftIO $ putStrLn (show res)

    if satisfiable res
    then do
        let m = fromJust (model res)
        let leaves = map makePathTree (gtLeaves gt)
        moves <- mapM (getMove player spec dMap copyMap m) leaves
        let paths = map (uncurry (fixPlayerMoves player)) (zip leaves moves)
        let cand = merge paths
        return (Just cand)
    else do
        return Nothing

merge (t:[]) = t
merge (t:ts) = foldl mergeTrees t ts

verify player spec s gt cand = do
    let og = projectMoves gt cand
    when (not (isJust og)) $ throwError "Error projecting, moves didn't match"
    let leaves = filter ((/= 0) . gtRank) (map makePathTree (gtLeaves (fromJust og)))
    let oppGames = map (\l -> appendChild l Nothing) leaves
    lift $ lift $ when (length oppGames > 0) logVerify
    mapMUntilJust (solveAbstract (opponent player) spec s) oppGames

---playOpponent player spec s gt = do
---    res <- solveAbstract (opponent player) spec s gt
---    if isJust res
---    then return $ Just (gt, fromJust res)
---    else return Nothing

refine player gt cex = do
    let moves = gtPathMoves cex
    if isJust moves
    then return $ appendNextMove gt (fromJust moves)
    else throwError "Non-path cex given to refine"

driverFml spec player s gt       = makeFml spec player s gt rootToLeafD
environmentFml spec player s gt  = makeFml spec player s gt rootToLeafE

makeFml spec player s gt rootToLeaf = do
    let rank = gtBaseRank gt
    let leaves = gtLeaves gt

    base <- rootToLeaf spec rank
    fmls <- mapM (renameAndFix spec player s base) leaves
    chains <- makeChains spec (gtRoot gt)
    liftIO $ putStrLn (printTree gt)
    liftIO $ putStrLn (show chains)
    let copyMap = zip (map gtMoves leaves) (map fst fmls)
    f <- conjunct (map snd fmls)
    return (copyMap, f)

moveToExpression :: Monad m => Move -> ExpressionT m (Maybe Expression)
moveToExpression Nothing    = return Nothing
moveToExpression (Just a)   = do
    e <- assignmentToExpression a
    return (Just e)

makeChains spec gt = let rank = gtRank gt in
    case gtChildren gt of
        []  -> if rank == 0
            then return $ (g spec) !! 0
            else rootToLeafD spec rank
        cs  -> do
            steps <- mapM (uncurry (makeStep rank spec)) cs
            let (first : rest) = steps
            let dontRename = map (setVarRank rank) (svars spec)
            rest' <- mapM (makeCopy dontRename) rest
            conjunct (first : map snd rest')


makeStep rank spec m c = do
    let CompiledSpec{..} = spec
    let i = rank - 1
            
    next <- makeChains spec c
    goal <- disjunct [next, (g !! i)]
    m' <- moveToExpression m
    move <- case m' of
        (Just move) -> return move
        Nothing     -> trueExpr
    conjunct [t !! i, vu !! i, vc !! i, goal, move]

-- Ensures that a player can't force the other player into an invalid move
makeHatMove (m, valid) = do
    if isJust m
    then do
        let (Just m') = m
        move <- assignmentToExpression m'
        move_hat <- setHatVar move
        valid_hat <- setHatVar valid
        imp <- implicate valid_hat move
        c <- conjunct [move_hat, imp]
        return (Just c)
    else
        return Nothing

renameAndFix spec player fml s leaf = do
    let vs = if player == Existential 
        then reverse (vu spec)
        else reverse (vc spec)

    myMoves <- mapM assignmentToExpression (catMaybes (gtMovesFor player leaf))
    let oppMoves' = gtMovesFor (opponent player) leaf
    oppMoves <- mapM makeHatMove (zip oppMoves' vs)
    conj <- conjunct ([s, fml] ++ myMoves ++ (catMaybes oppMoves))
    makeCopy [] conj 

rootToLeafD spec rank = do
    let CompiledSpec{..} = spec

    let i = rank - 1

    goal <- if rank == 1
        then return (g !! i)
        else do
            next <- rootToLeafD spec (rank-1)
            disjunct [next, (g !! i)]

    conjunct [t !! i, vu !! i, vc !! i, goal]

rootToLeafE spec rank = do
    let CompiledSpec{..} = spec

    let i = rank - 1

    goal <- if rank == 1
        then negation (g !! i)
        else do
            ng <- negation (g !! i)
            next <- rootToLeafE spec (rank-1)
            conjunct [next, ng]

    conjunct [t !! i, vu !! i, vc !! i, goal]

saveMove player spec dMap copyMap model gt = do
    let vs = if player == Existential then vc spec else vu spec
    valid <- isMoveValid gt vs dMap copyMap model
    if not valid
    then return Nothing
    else do
        move <- getMove player spec dMap copyMap model gt
        return $ Just (gtCrumb gt, Just move)

getMove player spec dMap copyMap model gt = do
    let vars = if player == Existential then cont spec else ucont spec
    let maxrnk = gtBaseRank gt
    let (Just cpy) = lookup (gtMoves gt) copyMap
    mapM (getMoveAtRank vars dMap cpy model) (reverse [1..maxrnk])

getMoveAtRank vars dMap cpy model rnk = do
    -- Change the rank 0/copy 0 vars to the vars we need
    let vars' = map (\v -> v {rank = rnk}) vars

    -- Lookup the indices of these vars in the Expression monad
    ve <- mapM lookupVar vars'

    -- Lookup the dimacs equivalents to these indices
    let vd = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vars'

    -- Finally, construct assignments
    return $ map (makeAssignment . (mapFst (\i -> model !! (i-1)))) vd

isMoveValid gt vs dMap copyMap model = do
    let r = gtRank gt
    let (Just c) = lookup (gtMoves gt) copyMap
    let vi = exprIndex (vs !! (r - 1))
    v <- lookupExpression vi
    let d = fromJust $ Map.lookup (c, exprIndex (fromJust v)) dMap
    let m = model !! (d - 1)
    return $ m > 0

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . left
