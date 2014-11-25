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
---    liftIO $ putStrLn ("Solve abstract for " ++ show player)
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

    (copyMap, fml) <- makeFml spec player s gt
    (dMap, dimacs) <- toDimacs fml
    res <- liftIO $ satSolve (maximum $ Map.elems dMap) dimacs

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

refine player gt cex = do
    let moves = gtPathMoves cex
    if isJust moves
    then return $ appendNextMove gt (fromJust moves)
    else throwError "Non-path cex given to refine"

makeFml spec player s gt = do
    (fml, cMap) <- makeChains spec player (gtRoot gt)
    fml' <- conjunct [fml, s]
    return (cMap, fml')

makeChains spec player gt = let rank = gtRank gt in
    case gtChildren gt of
        []  -> do
            f <- leafToBottom spec player rank
            return (f, [])
        cs  -> do
            steps <- mapM (makeStep rank spec player (gtFirstPlayer gt)) (movePairs gt)

            let (first : rest) = map fst steps
            let dontRename = map (setVarRank rank) (svars spec)
            -- No need to copy the first fml
            rest' <- mapM (makeCopy dontRename) rest
            f <- conjunct (first : map snd rest')
            let cMap = zip (map (gtCrumb . snd) (tail cs)) (map fst rest') ++ concatMap snd steps
            return (f, cMap)

moveToExpression :: Monad m => Move -> ExpressionT m (Maybe Expression)
moveToExpression Nothing    = return Nothing
moveToExpression (Just a)   = do
    e <- assignmentToExpression a
    return (Just e)

movePairs gt = concatMap makePairs (gtChildren gt)
    where
    makePairs (m, c) = case gtChildren c of
        []  -> [(m, Nothing, Nothing)]
        cs  -> map (appendTuple m) cs
    appendTuple m (m', c') = (m, m', Just c')

makeStep rank spec player first (m1, m2, c) = do
    let CompiledSpec{..} = spec
    let i = rank - 1

    (next, cmap) <- if isJust c
        then makeChains spec player (fromJust c)
        else do
            f <- leafToBottom spec player (rank-1)
            return (f, [])

    g' <- goalFor player (g !! i)
    goal <- if player == Existential
        then disjunct [next, g']
        else conjunct [next, g']

    let vh = if player == Existential then vu else vc

    m1' <- if player == first
        then moveToExpression m1
        else makeHatMove (vh !! i) m1

    m2' <- if player == first
        then makeHatMove (vh !! i) m2
        else moveToExpression m2

    let moves = catMaybes [m1', m2']
    s <- conjunct ([t !! i, vu !! i, vc !! i, goal] ++ moves)
    return (s, cmap)

-- Ensures that a player can't force the other player into an invalid move
makeHatMove valid m = do
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

goalFor Existential g   = return g
goalFor Universal g     = negation g

leafToBottom spec player rank = do
    let CompiledSpec{..} = spec
    let i = rank - 1

    if rank == 0
    then goalFor player (g !! 0)
    else do
        goal <- if rank == 1
            then goalFor player (g !! i)
            else do
                next <- leafToBottom spec player (rank-1)
                g' <- goalFor player (g !! i)
                if player == Existential
                    then disjunct [next, g']
                    else conjunct [next, g']

        conjunct [t !! i, vu !! i, vc !! i, goal]

getMove player spec dMap copyMap model gt = do
    let vars = if player == Existential then cont spec else ucont spec
    let maxrnk = gtBaseRank gt
    let cpy = case lookup (gtCrumb gt) copyMap of
            (Just c)    -> c
            Nothing     -> 0
    mapM (getMoveAtRank vars dMap cpy model) (reverse [1..maxrnk])

getMoveAtRank vars dMap cpy model rnk = do
    let vars' = map (\v -> v {rank = rnk}) vars
    ve <- mapM lookupVar vars'
    -- Lookup the dimacs equivalents
    let vd = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vars'
    -- Construct assignments
    return $ map (makeAssignment . (mapFst (\i -> model !! (i-1)))) vd

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . left
