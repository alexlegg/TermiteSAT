{-# LANGUAGE RecordWildCards #-}
module Synthesise.Solver (
      checkRank
    , checkStrategy
    , checkInit
    , checkUniversalWin
    , LearnedStates(..)
    , LearningType(..)
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
    initDefaultMoves spec rnk s
    r <- solveAbstract Universal spec s (gtNew Existential rnk)
    
    satTime <- liftIO $ timeInSAT
    (intTime, eA, eB) <- liftIO $ timeInInterpolate
    liftIO $ putStrLn $ "timeInSAT = " ++ (show ((fromInteger $ round $ (satTime * 10)) / 10.0))
    liftIO $ putStrLn $ "timeInInterpolate = " ++ (show ((fromInteger $ round $ (intTime * 10)) / 10.0))
    liftIO $ putStrLn $ "timeInEnodeA = " ++ (show ((fromInteger $ round $ (eA * 10)) / 10.0))
    liftIO $ putStrLn $ "timeInEnodeB = " ++ (show ((fromInteger $ round $ (eB * 10)) / 10.0))

    liftLog (logRank rnk)

    return (isNothing r)

initDefaultMoves :: CompiledSpec -> Int -> Expression -> SolverT ()
initDefaultMoves spec rank s = do
    let gt = gtExtend (gtNew Existential rank)

    --Wipe moves from last loop
    ls <- get
    put $ ls { defaultUnMoves   = Map.empty 
             , defaultExMoves   = Map.empty }

    (_, fE, _)  <- makeFml spec Existential s gt True
    rE          <- satSolve (gtMaxCopy gt) Nothing fE


    defaultEx <- if satisfiable rE
        then do
            moves   <- mapM (getVarsAtRank (cont spec) (fromJust (model rE)) 0) [1..rank]
            return $ Map.fromList (zip [1..rank] moves)
        else do
            -- No way to win at this rank so set anything
            let someExMove = map (\v -> Assignment Pos v) (cont spec)
            return $ foldl (\m r -> Map.insert r someExMove m) Map.empty [1..rank]

    (_, fU, _)  <- makeFml spec Universal s gt True
    rU          <- satSolve (gtMaxCopy gt) Nothing fU

    defaultUn <- if satisfiable rU
        then do
            moves   <- mapM (getVarsAtRank (ucont spec) (fromJust (model rU)) 0) [1..rank]
            return $ Map.fromList (zip [1..rank] moves)
        else do
            -- No way to win at this rank so set anything
            let someUnMove  = map (\v -> Assignment Pos v) (ucont spec)
            return $ foldl (\m r -> Map.insert r someUnMove m) Map.empty [1..rank]

    ls <- get
    put $ ls { defaultUnMoves   = defaultUn
             , defaultExMoves   = defaultEx }

checkInit :: Int -> Expression -> [[Assignment]] -> Expression -> SolverT Bool
checkInit k init must goal = do
    fml     <- makeInitCheckFml k init must goal
    r       <- satSolve 0 Nothing fml
    return $ satisfiable r

checkUniversalWin :: CompiledSpec -> Int -> SolverT Bool
checkUniversalWin spec k = do
    ls <- get
    let wm1     = map (\i -> Map.lookup i (winningMay ls)) [1..k-1]
    let wm2     = map (\i -> Map.lookup i (winningMay ls)) [2..k-1]

    let unWins  = or (zipWith (==) wm1 wm2)

    rs <- forM (zip wm1 wm2) $ \(wmA, wmB) -> do
        let f   = map Set.toList . maybe [] Set.toList
        fml     <- makeUniversalWinCheckFml (f wmA) (f wmB)
        r       <- satSolve 0 Nothing fml
        return r

    return $ any (not . satisfiable) rs

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
    liftIO $ putStrLn ("Solve abstract for " ++ show player)
---    pLearn <- printLearnedStates spec player
    liftLog $ logSolve gt player []

    cand <- findCandidate player spec s gt

    res <- refinementLoop player spec s cand gt gt

    liftLog $ logSolveComplete res
    liftLog $ logDumpLog

    return res

refinementLoop :: Player -> CompiledSpec -> Expression -> Maybe GameTree -> GameTree -> GameTree -> SolverT (Maybe GameTree)
refinementLoop player spec s Nothing origGT absGt = do
    liftIO $ putStrLn ("Could not find a candidate for " ++ show player)
    return Nothing
refinementLoop player spec s (Just cand) origGT absGT = do
    v <- verify player spec s origGT cand
    case v of
        (Just cex) -> do
            liftIO $ putStrLn ("Counterexample found against " ++ show player)
            absGT' <- refine absGT cex
            liftLog $ logRefine
            cand' <- solveAbstract player spec s absGT'
            refinementLoop player spec s cand' origGT absGT'
        Nothing -> do
            liftIO $ putStrLn ("Verified candidate for " ++ show player)
            return (Just cand)
    

findCandidate :: Player -> CompiledSpec -> Expression -> GameTree -> SolverT (Maybe GameTree)
findCandidate player spec s gt = do
    (es, f, gt')    <- makeFml spec player s gt True
    res             <- satSolve (gtMaxCopy gt') Nothing f

    fp <- liftE $ printExpression f
    liftIO $ writeFile ("fml" ++ show player) fp

    dumpDimacs (gtMaxCopy gt') f ("dimacs" ++ show player)

    if satisfiable res
    then do
        (Just m)    <- shortenStrategy player gt' f (model res) es
        gt'         <- setMoves player spec m (gtRoot gt')
        outGt'      <- setMoves player spec m (gtRoot (gtExtend gt'))
        liftLog $ logCandidate (Just outGt')
        return (Just gt')
    else do
        ls <- get
        if (learningType ls == BoundedLearning)
        then do
            mapM_ (learnStates spec player) (gtUnsetNodes gt)
        else do
            learnWinning spec player s gt
            --mapM_ (learnStates spec player) (gtUnsetNodes gt)
        liftLog $ logCandidate Nothing
        return Nothing

learnStates :: CompiledSpec -> Player -> GameTree -> SolverT ()
learnStates spec player ogt = do
    let gt'         = gtRebase 0 ogt
    let (Just as)   = gtPrevState ogt
    let rank        = gtBaseRank gt'
    let s           = map (\x -> setAssignmentRankCopy x rank 0) as

    fakes           <- liftE $ trueExpr
    (es, f, gt)     <- makeFml spec player fakes gt' True
    cores           <- minimiseCore gt (Just s) f

    when (isJust cores) $ do
        cs          <- mapM (\core -> getConflicts (svars spec) core 0 rank) (fromJust cores)
        let cube    = map (sort . map (\a -> setAssignmentRankCopy a 0 0)) cs

---        liftIO $ putStrLn $ "--learnStates for " ++ show player ++ " " ++ (show rank) ++ "--"
---        liftIO $ mapM (putStrLn . printMove spec . Just) cube
---        liftIO $ putStrLn $ "--learnStates for " ++ show player ++ "--"

        ls <- get
        if player == Existential
        then do
            put $ ls { winningMay    = alterAll (insertIntoSet cube) [1..rank] (winningMay ls) }
            liftLog $ logLosingState (printMove spec (Just (head cube)))
        else do
            put $ ls { winningMust   = foldl insertCube (winningMust ls) cube }
            liftLog $ logLosingState (printMove spec (Just (head cube)))

getLosingStates :: CompiledSpec -> Player -> GameTree -> SolverT (Maybe [[Assignment]])
getLosingStates spec player ogt = do
    let gt'         = gtRebase 0 ogt
    let (Just as)   = gtPrevState ogt
    let rank        = gtBaseRank gt'
    let s           = map (\x -> setAssignmentRankCopy x rank 0) as

    fakes           <- liftE $ trueExpr
    (es, f, gt)     <- makeFml spec player fakes gt' True
    cores           <- minimiseCore gt (Just s) f


    if (isJust cores)
    then do
        cs <- mapM (\core -> getConflicts (svars spec) core 0 rank) (fromJust cores)
        return $ Just cs
    else 
        return Nothing


learnWinning :: CompiledSpec -> Player -> Expression -> GameTree -> SolverT ()
learnWinning spec player s gt = do
    sp <- liftE $ printExpression s
    let gts = gtUnsetNodes gt
    (s', gt') <- case gts of
        []      -> return $ (s, gt)
        (t:[])  -> do
            core        <- getLosingStates spec player t
            case core of
                (Just c) -> do
                    coreExps    <- liftE $ mapM (assignmentToExpression 0) c
                    allCores    <- liftE $ disjunct coreExps
                    return $ (allCores, gtRebase 0 t)
                Nothing -> do
                    coreExp     <- liftE $ trueExpr
                    return (coreExp, gtRebase 0 t)
        _       -> throwError "I think this is an error?"


    interpolateTree spec player s' (gtExtend gt')

interpolateTree :: CompiledSpec -> Player -> Expression -> GameTree -> SolverT ()
interpolateTree spec player s gt' = do
    let gt = normaliseCopies gt'
    fmls <- makeSplitFmls spec player s gt
    if (isJust fmls)
    then do
        let Just (gtA, gtB, fmlA, fmlB) = fmls

        let vRank   = gtRank gtB
        let vCopy   = gtCopyId (gtRoot gtB)
        let vars    = map (\v -> v {rank = vRank, ecopy = vCopy}) (svars spec)
        project     <- liftE $ mapM (fmap (exprIndex . fromJust) . lookupVar) vars

        rA <- satSolve (gtMaxCopy gt) Nothing fmlA

        if (not (satisfiable rA))
        then do
            -- We lose in the prefix, so just keep going
            interpolateTree spec player s gtA
        else do
            ir <- interpolate (gtMaxCopy gt) project fmlA fmlB
            if (not (success ir))
            then do
                sp <- liftE $ printExpression s
                liftIO $ putStrLn sp
                liftIO $ putStrLn (printTree spec gtA)
                liftIO $ putStrLn (printTree spec gtB)
                throwError "Interpolation failed"
            else do
                let cube'   = map (filter (((==) StateVar) . assignmentSection)) (fromJust (interpolant ir))
                let cube''  = filter (all (\a -> assignmentRank a == gtRank gtB)) cube'
                let cube    = map (sort . map (\a -> setAssignmentRankCopy a 0 0)) cube''
                
---                liftIO $ putStrLn $ "--Losing for " ++ show player ++ " " ++ (show (gtBaseRank gtB)) ++ "--"
---                liftIO $ mapM (putStrLn . printMove spec . Just) cube
---                liftIO $ putStrLn $ "--Losing for " ++ show player ++ "--"
---                liftIO $ putStrLn ""
--
---                liftIO $ mapM (\c -> putStrLn $ "learnWinning " ++ show c) cube

                when (any (\cs -> not $ all (\a -> assignmentRank a == assignmentRank (head cs)) cs) cube') $ do
                    throwError "Not all cubes of the same rank"

                when (any (\cs -> not $ all (\a -> assignmentCopy a == assignmentCopy (head cs)) cs) cube') $ do
                    throwError "Not all cubes of the same copy"

                ls <- get
                if player == Existential
                then put $ ls {
                      winningMay    = alterAll (insertIntoSet cube) [1..gtBaseRank gtB] (winningMay ls)
                    }
                else put $ ls {
                      winningMust   = foldl insertCube (winningMust ls) cube 
                    }

                interpolateTree spec player s gtA
    else return ()

alterAll :: Ord k => (Maybe a -> Maybe a) -> [k] -> Map.Map k a -> Map.Map k a
alterAll f (k:[]) m = Map.alter f k m
alterAll f (k:ks) m = Map.alter f k (alterAll f ks m)

insertIntoSet :: Ord a => [[a]] -> Maybe (Set.Set (Set.Set a)) -> Maybe (Set.Set (Set.Set a))
insertIntoSet xs ss = Just $ foldl insertCube (fromMaybe Set.empty ss) xs

insertCube :: Ord a => Set.Set (Set.Set a) -> [a] -> Set.Set (Set.Set a)
insertCube ss x' = let x = Set.fromList x' in
    if isJust $ find (\s -> s `Set.isSubsetOf` x) ss
        then ss 
        else Set.insert x $ Set.filter (\s -> not (x `Set.isSubsetOf` s)) ss

printLearnedStates :: CompiledSpec -> Player -> SolverT [String]
printLearnedStates spec player = do
    LearnedStates{..} <- get
    if player == Existential
    then do
        return $ map (\(k, e) -> printMove spec (Just e)) (ungroupZip (map (mapSnd (\s -> map Set.toList (Set.toList s))) (Map.toList winningMay)))
    else do
        return $ map (printMove spec . Just) (map Set.toList (Set.toList winningMust))

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
    res         <- satSolve (gtMaxCopy gt) Nothing fml'
    if satisfiable res
    then do
        shortenLeaf gt (fml', model res) es
    else do
        return (fml, m)
shortenLeaf _ (fml, m) [] = return (fml, m)
