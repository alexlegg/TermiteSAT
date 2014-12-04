{-# LANGUAGE RecordWildCards #-}
module Synthesise.Solver (
    checkRank
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
import Synthesise.GameTree
import SatSolver.SatSolver
import Utils.Logger
import Utils.Utils

checkRank :: CompiledSpec -> Int -> Expression -> ExpressionT (LoggerT IO) Bool
checkRank spec rnk s = do
    r <- solveAbstract Universal spec s (gtNew Existential rnk)
    return (isNothing r)

solveAbstract :: Player -> CompiledSpec -> Expression -> GameTree -> ExpressionT (LoggerT IO) (Maybe GameTree)
solveAbstract player spec s gt = do
---    liftIO $ putStrLn ("Solve abstract for " ++ show player)
    cand <- findCandidate player spec s gt
    liftLog $ logSolve gt cand player
    res <- refinementLoop player spec s cand gt gt
    liftLog $ logSolveComplete res
---    liftLog $ logDumpLog
    return res

refinementLoop :: Player -> CompiledSpec -> Expression -> Maybe GameTree -> GameTree -> GameTree -> ExpressionT (LoggerT IO) (Maybe GameTree)
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
    

findCandidate :: Player -> CompiledSpec -> Expression -> GameTree -> ExpressionT (LoggerT IO) (Maybe GameTree)
findCandidate player spec s gt = do
    (fml, copyMap) <- makeFml spec player s gt
    (dMap, dimacs) <- toDimacs fml
    res <- liftIO $ satSolve (maximum $ Map.elems dMap) dimacs

    if satisfiable res
    then do
        let (Just m)    = model res
        let leaves      = gtLeaves gt
        init            <- getVarsAtRank (svars spec) dMap m 0 (gtBaseRank gt)
        moves           <- mapM (getMove player spec dMap copyMap m) leaves
        let paths       = zipWith (fixPlayerMoves player) (map makePathTree leaves) moves
        return (Just (merge (map (fixInitState init) paths)))
    else do
        learning <- mapM (learnStates spec player) (gtUnsetNodes gt)

---        liftIO $ withFile "debug_dimacs" WriteMode $ \h -> do
---            hPutStrLn h $ "p cnf " ++ (show (maximum (Map.elems dMap))) ++ " " ++ (show (length dimacs))
---            mapM ((hPutStrLn h) . (\x -> x ++ " 0") . (interMap " " show)) dimacs

---        liftIO $ putStrLn (show (conflicts res))
        return Nothing

learnStates spec player gt = do
    let ass = gtPrevState gt
    let gt' = gtRebase gt

    fakes <- trueExpr
    (fml, copyMap) <- makeFml spec player fakes gt'
    (dMap, dimacs) <- toDimacs fml
    res <- liftIO $ satSolve (maximum $ Map.elems dMap) dimacs

    liftIO $ putStrLn (show (satisfiable res))

    return Nothing

merge (t:[]) = t
merge (t:ts) = foldl mergeTrees t ts

verify player spec s gt cand = do
    let og = projectMoves gt cand
    when (not (isJust og)) $ throwError "Error projecting, moves didn't match"
    let leaves = filter ((/= 0) . gtRank) (map makePathTree (gtLeaves (fromJust og)))
    mapMUntilJust (verifyLoop (opponent player) spec s) (zip [0..] leaves)

verifyLoop player spec s (i, gt) = do
    liftLog $ logVerify i
    let oppGame = appendChild gt
    solveAbstract player spec s oppGame

refine gt cex = case (gtPathMoves cex) of
    (Just moves)    -> return $ appendNextMove gt moves
    Nothing         -> throwError "Non-path cex given to refine"

makeFml spec player s gt = do
    let root    = gtRoot gt
    let rank    = gtRank root
    initMove    <- moveToExpression (gtMove root)
    s'          <- maybeM s (\i -> conjunct [s, i]) initMove

    if null (gtChildren root)
    then do
        fml         <- leafToBottom spec player rank
        fml'        <- conjunct [fml, s']

        return (fml', [])
    else do
        let cs      = concatMap (gtMovePairs . snd) (gtChildren root)
        steps       <- mapM (makeStep rank spec player (gtFirstPlayer gt)) cs
        (fml, cMap) <- mergeRenamed spec rank (map thd3 cs) (map fst steps)
        fml'        <- conjunct [fml, s']

        return (fml', cMap ++ concatMap snd steps)

mergeRenamed spec rank gts (f:[]) = return (f, [])
mergeRenamed spec rank gts (f:fs) = do
    let dontRename  = map (setVarRank rank) (svars spec)
    (copies, fs')   <- unzipM (mapM (makeCopy dontRename) fs)
    fml             <- conjunct (f : fs')

    let cMap = zip (map (groupCrumb . gtCrumb) (map fromJust (tail gts))) copies
    return (fml, cMap)

makeStep rank spec player first (m1, m2, c) = do
    let CompiledSpec{..} = spec
    let i = rank - 1

    (next, cmap) <- if isJust c
        then do
            let cs = concatMap (gtMovePairs . snd) (gtChildren (fromJust c))
            if null cs
            then do
                f <- leafToBottom spec player (rank-1)
                return (f, [])
            else do
                steps <- mapM (makeStep (rank-1) spec player first) cs
                (f, cMap') <- mergeRenamed spec (rank-1) (map thd3 cs) (map fst steps)
                return (f, concatMap snd steps ++ cMap')
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

moveToExpression :: Monad m => Move -> ExpressionT m (Maybe Expression)
moveToExpression Nothing    = return Nothing
moveToExpression (Just a)   = do
    e <- assignmentToExpression a
    return (Just e)


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

    when (rank < 0) $ throwError "leafToBottom called on a tree that's too long"

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
    let copies = tail $ foldl getCpy [0] (tail (inits (groupCrumb (gtCrumb gt))))
    let rankCopies = zip (copies ++ replicate (maxrnk - (length copies)) 0) (reverse [1..maxrnk])
    states <- mapM (uncurry (getVarsAtRank (svars spec) dMap model)) (map (mapSnd (\r -> r - 1)) rankCopies)
    moves <- mapM (uncurry (getVarsAtRank vars dMap model)) rankCopies
    return $ zip moves states
    where
        getCpy p crumb = p ++ [fromMaybe (last p) (lookup crumb copyMap)]

groupCrumb []          = []
groupCrumb (m1:[])     = [(m1,0)]
groupCrumb (m1:m2:ms)  = (m1,m2) : groupCrumb ms

getVarsAtRank vars dMap model cpy rnk = do
    let vars' = map (\v -> v {rank = rnk}) vars
    ve <- mapM lookupVar vars'
    -- Lookup the dimacs equivalents
    let vd = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vars'
    -- Construct assignments
    return $ map (makeAssignment . (mapFst (\i -> model !! (i-1)))) vd

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . left

liftLog = lift . lift
