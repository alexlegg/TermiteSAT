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
import Synthesise.GameTree
import SatSolver.SatSolver
import Utils.Logger
import Utils.Utils

type SolverST m = StateT LearnedStates m
type SolverT = SolverST (ExpressionT (LoggerT IO))

data LearnedStates = LearnedStates {
      winningEx :: [[Assignment]]
    , winningUn :: Map.Map Int [[Assignment]]
}

emptyLearnedStates = LearnedStates {
      winningEx = []
    , winningUn = Map.empty
}

throwError = lift . lift . left

liftLog :: LoggerT IO a -> SolverT a
liftLog = lift . lift . lift

liftE :: ExpressionT (LoggerT IO) a -> SolverT a
liftE = lift

checkRank :: CompiledSpec -> Int -> Expression -> SolverT Bool
checkRank spec rnk s = do
    r <- solveAbstract Universal spec s (gtNew Existential rnk)
    return (isNothing r)

solveAbstract :: Player -> CompiledSpec -> Expression -> GameTree -> SolverT (Maybe GameTree)
solveAbstract player spec s gt = do
---    liftIO $ putStrLn ("Solve abstract for " ++ show player)
    liftLog $ logSolve gt player
    cand <- findCandidate player spec s gt
    liftLog $ logCandidate cand
    res <- refinementLoop player spec s cand gt gt
    liftLog $ logSolveComplete res
---    liftLog $ logDumpLog
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
        let paths       = zipWith (fixPlayerMoves player) (map makePathTree leaves) moves
        return (Just (merge (map (fixInitState init) paths)))
    else do
        mapM_ (learnStates spec player) (gtUnsetNodes gt)
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
    then throwError $ "Not handling this case yet"
    else do
        noAssumps <- liftIO $ satSolve (maximum $ Map.elems dMap) [] d

        if (satisfiable noAssumps)
        then do
            c <- getConflicts (svars spec) dMap (fromJust (conflicts res)) 0 rank
            ls <- get
            liftLog $ logLosingState (printPartialAssignment (vinfo spec) c)
            if player == Existential
            then put $ ls { winningUn = Map.alter (\x -> Just (fromMaybe [] x ++ [c])) rank (winningUn ls) }
            else put $ ls { winningEx = winningEx ls ++ [c] }
        else do
            -- Player loses for all states here
            -- TODO Learn something
            return ()

printPartialAssignment :: [VarInfo] -> [Assignment] -> String
printPartialAssignment vinfo as = interMap ", " (printPartialVar vinfo) (groupBy f as)
    where f (Assignment _ x) (Assignment _ y) = varname x == varname y

printPartialVar :: [VarInfo] -> [Assignment] -> String
printPartialVar vinfo as = show size
    where
        size = sz (fromJust (find (\v -> name v == aname (head as)) vinfo))
        aname (Assignment _ v)  = varname v

verify :: Player -> CompiledSpec -> Expression -> GameTree -> GameTree -> SolverT (Maybe GameTree)
verify player spec s gt cand = do
    let og = projectMoves gt cand
    when (not (isJust og)) $ throwError "Error projecting, moves didn't match"
    let leaves = filter ((/= 0) . gtRank) (map makePathTree (gtLeaves (fromJust og)))
    mapMUntilJust (verifyLoop (opponent player) spec s) (zip [0..] leaves)

verifyLoop :: Player -> CompiledSpec -> Expression -> (Int, GameTree) -> SolverT (Maybe GameTree)
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
    initMove    <- liftE $ moveToExpression (gtMove root)
    s'          <- liftE $ maybeM s (\i -> conjunct [s, i]) initMove

    if null (gtChildren root)
    then do
        fml         <- leafToBottom spec player rank
        fml'        <- liftE $ conjunct [fml, s']

        return (fml', [])
    else do
        let cs      = concatMap (gtMovePairs . snd) (gtChildren root)
        steps       <- mapM (makeStep rank spec player (gtFirstPlayer gt)) cs
        (fml, cMap) <- mergeRenamed spec rank (map thd3 cs) (map fst steps)
        fml'        <- liftE $ conjunct [fml, s']

        return (fml', cMap ++ concatMap snd steps)

mergeRenamed spec rank gts (f:[]) = return (f, [])
mergeRenamed spec rank gts (f:fs) = do
    let dontRename  = map (setVarRank rank) (svars spec)
    (copies, fs')   <- liftE $ unzipM (mapM (makeCopy dontRename) fs)
    fml             <- liftE $ conjunct (f : fs')

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

    g' <- liftE $ goalFor player (g !! i)
    goal <- if player == Existential
        then liftE $ disjunct [next, g']
        else liftE $ conjunct [next, g']

    let vh = if player == Existential then vu else vc

    m1' <- if player == first
        then liftE $ moveToExpression m1
        else liftE $ makeHatMove (vh !! i) m1

    m2' <- if player == first
        then liftE $ makeHatMove (vh !! i) m2
        else liftE $ moveToExpression m2

    block <- blockLosingStates rank player

    let moves = catMaybes [m1', m2', block]
    s <- liftE $ conjunct ([t !! i, vu !! i, vc !! i, goal] ++ moves)
    return (s, cmap)

blockLosingStates rank player = do
    LearnedStates{..} <- get
    let block = if player == Existential
        then fromMaybe [] (Map.lookup rank winningUn)
        else winningEx

    if null block
    then return Nothing
    else do 
        bs <- liftE $ mapM blockAssignment block
        b <- liftE $ conjunct bs
        return (Just b)

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

leafToBottom :: CompiledSpec -> Player -> Int -> SolverT Expression
leafToBottom spec player rank = do
    let CompiledSpec{..} = spec
    let i = rank - 1

    when (rank < 0) $ throwError "leafToBottom called on a tree that's too long"

    if rank == 0
    then liftE $ goalFor player (g !! 0)
    else do
        goal <- if rank == 1
            then liftE $ goalFor player (g !! i)
            else do
                next <- leafToBottom spec player (rank-1)
                g' <- liftE $ goalFor player (g !! i)
                if player == Existential
                    then liftE $ disjunct [next, g']
                    else liftE $ conjunct [next, g']

        block <- blockLosingStates rank player
        if isJust block
        then liftE $ conjunct [t !! i, vu !! i, vc !! i, goal, fromJust block]
        else liftE $ conjunct [t !! i, vu !! i, vc !! i, goal]

getMove player spec dMap copyMap model gt = do
    let vars    = if player == Existential then cont spec else ucont spec
    let maxrnk  = gtBaseRank gt
    let copies  = tail $ foldl getCpy [0] (tail (inits (groupCrumb (gtCrumb gt))))
    let rCopies = zip (copies ++ replicate (maxrnk - (length copies)) 0) (reverse [1..maxrnk])
    states      <- mapM (uncurry (getVarsAtRank (svars spec) dMap model)) (map (mapSnd (\r -> r - 1)) rCopies)
    moves       <- mapM (uncurry (getVarsAtRank vars dMap model)) rCopies

    return $ zip moves states
    where
        getCpy p crumb = p ++ [fromMaybe (last p) (lookup crumb copyMap)]

groupCrumb []          = []
groupCrumb (m1:[])     = [(m1,0)]
groupCrumb (m1:m2:ms)  = (m1,m2) : groupCrumb ms

getVarsAtRank vars dMap model cpy rnk = do
    let vars' = map (\v -> v {rank = rnk}) vars
    ve <- liftE $ mapM lookupVar vars'
    -- Lookup the dimacs equivalents
    let vd = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vars'
    -- Construct assignments
    return $ map (makeAssignment . (mapFst (\i -> model !! (i-1)))) vd

getConflicts vars dMap conflicts cpy rnk = do
    let vs  = map (\v -> v {rank = rnk}) vars
    ve      <- liftE $ mapM lookupVar vs
    let vd  = zipMaybe1 (map (\v -> Map.lookup (cpy, exprIndex v) dMap) (catMaybes ve)) vs
    let cs  = map (\c -> (abs c, c)) conflicts
    let as  = map ((uncurry liftMFst) . mapFst (\i -> lookup i cs)) vd
    return  $ map makeAssignment (catMaybes as)

