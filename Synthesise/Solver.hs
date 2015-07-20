{-# LANGUAGE RecordWildCards, ViewPatterns #-}
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

checkRank :: CompiledSpec -> Int -> [Assignment] -> Maybe ([[Assignment]], [[Assignment]]) -> Maybe Int -> Shortening -> SolverT (Int, Bool)
checkRank spec rnk s def im short = do
---    initDefaultMoves spec rnk True s def 
---    initDefaultMoves spec rnk False s def
---    initDefaultMoves spec rnk False s def
---    initDefaultMoves spec rnk False s def
    r <- solveAbstract Universal spec s (gtNew Existential rnk) short

    satTime             <- liftIO $ timeInSAT
    satCalls            <- liftIO $ totalSATCalls
    (intTime, eA, eB)   <- liftIO $ timeInInterpolate

    liftLog $ putStrLnDbg 1 "----------------"
    liftLog $ putStrLnDbg 1 $ "timeInSAT = " ++ (show ((fromInteger $ round $ (satTime * 10)) / 10.0))
    liftLog $ putStrLnDbg 1 $ "SAT Calls = " ++ (show satCalls)
    liftLog $ putStrLnDbg 1 $ "timeInInterpolate = " ++ (show ((fromInteger $ round $ (intTime * 10)) / 10.0))
    liftLog $ putStrLnDbg 1 $ "timeInEnodeA = " ++ (show ((fromInteger $ round $ (eA * 10)) / 10.0))
    liftLog $ putStrLnDbg 1 $ "timeInEnodeB = " ++ (show ((fromInteger $ round $ (eB * 10)) / 10.0))
    liftLog $ putStrLnDbg 1 "----------------"

    liftLog (logRank rnk)

    extraSatCalls <- if (isJust im && isJust r && rnk <= fromJust im)
    then do
        let init    = fromJust (gtMove (gtRoot (snd (fromJust r))))
        (cube, sc)  <- tryReducedInit spec rnk 0 [] init short 0
        let cube'   = map (sort . map (\a -> setAssignmentRankCopy a 0 0)) [cube]

---        liftIO $ putStrLn (printMove spec (Just cube))

        ls <- get
        put $ ls {
            winningMay = alterAll (insertIntoSet cube') [1..rnk] (winningMay ls)
        }

        return sc
    else return 0

    liftIO $ putStrLn "==================================================="

    return (satCalls + extraSatCalls, isNothing r)

tryReducedInit _ _ _ cube [] _ sc                   = return (cube, sc)
tryReducedInit spec rnk a cube (cur:rem) short sc   = do
    let s = cube ++ rem
---    initDefaultMoves spec rnk True s Nothing
---    initDefaultMoves spec rnk False s Nothing
    r <- solveAbstract Existential spec s (appendChild (gtNew Existential rnk)) short

    satTime             <- liftIO $ timeInSAT
    satCalls            <- liftIO $ totalSATCalls
    (intTime, eA, eB)   <- liftIO $ timeInInterpolate

    liftLog $ putStrLnDbg 2 "----------------"
    liftLog $ putStrLnDbg 2 "Expand Init"
    liftLog $ putStrLnDbg 2 (printMove spec (Just cube))
    liftLog $ putStrLnDbg 2 $ "timeInSAT = " ++ (show ((fromInteger $ round $ (satTime * 10)) / 10.0))
    liftLog $ putStrLnDbg 2 $ "SAT Calls = " ++ (show satCalls)
    liftLog $ putStrLnDbg 2 $ "timeInInterpolate = " ++ (show ((fromInteger $ round $ (intTime * 10)) / 10.0))
    liftLog $ putStrLnDbg 2 $ "timeInEnodeA = " ++ (show ((fromInteger $ round $ (eA * 10)) / 10.0))
    liftLog $ putStrLnDbg 2 $ "timeInEnodeB = " ++ (show ((fromInteger $ round $ (eB * 10)) / 10.0))
    liftLog $ putStrLnDbg 2 "----------------"
    liftLog (logRankAux rnk a)

    if isJust r
        then tryReducedInit spec rnk (a+1) (cube ++ [cur]) rem short (sc + satCalls)
        else tryReducedInit spec rnk (a+1) cube rem short (sc + satCalls)
    

initDefaultMoves :: CompiledSpec -> Int -> Bool -> [Assignment] -> Maybe ([[Assignment]], [[Assignment]]) -> SolverT ()
initDefaultMoves spec rank wipe s (Just (uMoves, eMoves)) = do
---    liftIO $ mapM (putStrLn . (printMove spec) . Just) (take rank uMoves)
---    liftIO $ mapM (putStrLn . (printMove spec) . Just) (take rank eMoves)
    let defaultUn = zipWith (\r m -> (r, map (\a -> setAssignmentRankCopy a r 0) m)) [1..rank] uMoves
    let defaultEx = zipWith (\r m -> (r, map (\a -> setAssignmentRankCopy a r 0) m)) [1..rank] eMoves
    ls <- get
    put $ ls { defaultUnMoves   = Map.fromList defaultUn
             , defaultExMoves   = Map.fromList defaultEx
             }
    return ()
initDefaultMoves spec rank wipe s Nothing = do
    let gt = gtExtend (gtNew Existential rank)

    --Wipe moves from last loop
    when (wipe) $ do
        ls <- get
        put $ ls { defaultUnMoves   = Map.empty 
                 , defaultExMoves   = Map.empty }

    (_, fE, _)  <- makeFml spec Existential s gt True False
    rE          <- satSolve (gtMaxCopy gt) Nothing fE

    ls <- get
    defaultEx <- if satisfiable rE
        then do
            moves   <- mapM (getVarsAtRank ContVar (fromJust (model rE)) 0) [1..rank]
            gtTest  <- setMoves Existential spec (fromJust (model rE)) (gtRoot gt)
---            liftIO $ putStrLn "Existential"
---            liftIO $ putStrLn (printTree spec gtTest)
            return $ Map.fromList (zip [1..rank] moves)
        else do
            -- No way to win at this rank against opp default moves
---            liftIO $ putStrLn "Ex no way to win"
            if Map.null (defaultExMoves ls)
            then do
                let someExMove = map (\v -> Assignment Pos v) (cont spec)
                return $ foldl (\m r -> Map.insert r someExMove m) Map.empty [1..rank]
            else do
                return $ defaultExMoves ls

    ls <- get
    put $ ls { defaultExMoves   = defaultEx }

    (_, fU, _)  <- makeFml spec Universal s gt True False
    rU          <- satSolve (gtMaxCopy gt) Nothing fU

    defaultUn <- if satisfiable rU
        then do
            moves   <- mapM (getVarsAtRank UContVar (fromJust (model rU)) 0) [1..rank]
            gtTest  <- setMoves Universal spec (fromJust (model rU)) (gtRoot gt)
---            liftIO $ putStrLn "Universal"
---            liftIO $ putStrLn (printTree spec gtTest)
            return $ Map.fromList (zip [1..rank] moves)
        else do
            -- No way to win at this rank against opp default moves
---            liftIO $ putStrLn "Un no way to win"
            if Map.null (defaultUnMoves ls)
            then do
                let someUnMove  = map (\v -> Assignment Pos v) (ucont spec)
                return $ foldl (\m r -> Map.insert r someUnMove m) Map.empty [1..rank]
            else do
                return $ defaultUnMoves ls

---    liftIO $ mapM (putStrLn . (printMove spec) . Just) defaultEx
---    liftIO $ mapM (putStrLn . (printMove spec) . Just) defaultUn

    ls <- get
    put $ ls { defaultUnMoves   = defaultUn }

checkInit :: Int -> [Assignment] -> [[Assignment]] -> Expression -> SolverT Bool
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

checkStrategy :: CompiledSpec -> Int -> [Assignment] -> String -> Tree [[Assignment]] -> SolverT Bool
checkStrategy spec rnk s player strat = do
    let p       = if player == "universal" then Universal else Existential
    let gt      = buildStratGameTree p (gtNew Existential rnk) strat
    r           <- solveAbstract Universal spec s gt ShortenNone
    liftIO $ putStrLn "Playing Strategy from file:"
    liftIO $ putStrLn (printTree spec gt)
    return (isNothing r)

buildStratGameTree player gt strat = gtParent $ gtParent $ foldl (buildStratGameTree player) gt' (subForest strat)
    where
        append  = if player == Existential then gtAppendMove else gtAppendMoveU
        gt'     = append gt (Just (concat (rootLabel strat)))

solveAbstract :: Player -> CompiledSpec -> [Assignment] -> GameTree -> Shortening -> SolverT (Maybe (GameTree, GameTree))
solveAbstract player spec s gt short = do
---    liftIO $ putStrLn ("Solve abstract for " ++ show player)
---    pLearn <- printLearnedStates spec player
    liftLog $ logSolve gt player []

    cand <- findCandidate player spec s short gt

    res <- refinementLoop player spec s short cand gt gt

    liftLog $ logSolveComplete (fmap snd res)
    liftLog $ logDumpLog

    return res

refinementLoop :: Player -> CompiledSpec -> [Assignment] -> Shortening -> Maybe (GameTree, GameTree) -> GameTree -> GameTree -> SolverT (Maybe (GameTree, GameTree))
refinementLoop player spec s short Nothing origGT absGt = do
---    liftIO $ putStrLn ("Could not find a candidate for " ++ show player)
    return Nothing
refinementLoop player spec s short (Just (wholeGt, cand)) origGT absGT = do
    v <- verify player spec s short origGT cand
    case v of
        (Just cex) -> do
---            liftIO $ putStrLn ("Counterexample found against " ++ show player)
            absGT' <- refine absGT cex
            liftLog $ logRefine
            cand' <- solveAbstract player spec s absGT' short
            refinementLoop player spec s short cand' origGT absGT'
        Nothing -> do
---            liftIO $ putStrLn ("Verified candidate for " ++ show player)

            -- Try to learn bad moves from the bad candidate
            learnBadMoves spec player wholeGt

            return (Just (wholeGt, cand))
    

findCandidate :: Player -> CompiledSpec -> [Assignment] -> Shortening -> GameTree -> SolverT (Maybe (GameTree, GameTree))
findCandidate player spec s short gt = do
    (es, f, gt')    <- makeFml spec player s gt True False
    res             <- satSolve (gtMaxCopy gt') Nothing f

    if satisfiable res
    then do
        (Just m)    <- shortenStrategy short player spec s gt' f (model res) es
---        let (Just oModel) = model res
---        let Just m  = model res
---        unShortened <- setMoves player spec oModel (gtRoot gt')
        gt'         <- setMoves player spec m (gtRoot gt')
        outGt'      <- setMoves player spec m (gtRoot (gtExtend gt'))
        wholeGt     <- setMoves (opponent player) spec m outGt'
        
---        when (player == Universal && oModel /= m) $ do
---            origGt' <- setMoves player spec oModel (gtRoot (gtExtend gt'))
---            liftIO $ putStrLn (printTree spec wholeGt)
---            liftIO $ putStrLn (printTree spec origGt')

        liftLog $ logCandidate (Just outGt')
        return (Just (wholeGt, gt'))
    else do
---        liftIO $ putStrLn $ "losing candidate " ++ show player
---        when (player == Existential) $ liftIO $ putStrLn $ "Losing candidate"
        ls <- get
        if (learningType ls == BoundedLearning)
            then mapM_ (learnStates spec player) (gtUnsetNodes gt)
            else learnWinning spec player s gt

        liftLog $ logCandidate Nothing
        return Nothing

learnStates :: CompiledSpec -> Player -> GameTree -> SolverT ()
learnStates spec player ogt = do
    let gt'         = gtRebase 0 ogt
    let (Just as)   = gtPrevState ogt
    let rank        = gtBaseRank gt'
    let s           = map (\x -> setAssignmentRankCopy x rank 0) as

    (es, f, gt)     <- makeFml spec player [] gt' True False
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
            liftLog $ logLosingState (head cube)
        else do
            put $ ls { winningMust   = foldl insertCube (winningMust ls) cube }
            liftLog $ logLosingState (head cube)

getLosingStates :: CompiledSpec -> Player -> GameTree -> SolverT (Maybe [[Assignment]])
getLosingStates spec player ogt = do
    let gt'         = gtRebase 0 ogt
    let (Just as)   = gtPrevState ogt
    let rank        = gtBaseRank gt'
    let s           = map (\x -> setAssignmentRankCopy x rank 0) as

    (es, f, gt)     <- makeFml spec player [] gt' True False
    cores           <- minimiseCore gt (Just s) f

    if (isJust cores)
    then do
        cs <- mapM (\core -> getConflicts (svars spec) core 0 rank) (fromJust cores)
        return $ Just cs
    else 
        return Nothing

dbgOutNoLearning :: CompiledSpec -> Player -> [Assignment] -> GameTree -> Bool -> SolverT ()
dbgOutNoLearning spec player s gt found = do
---    liftIO $ putStrLn ("interpolateTree" ++ show found)
---    when (not found) $ do
---        if (player == Existential)
---            then do
---                ls <- get
---                forM (Map.toList (winningMay ls)) $ \(r, wm) -> do
---                    liftIO $ putStrLn (show r)
---                    forM (Set.toList wm) $ \s ->
---                        liftIO $ putStrLn (printMove spec (Just (sort (Set.toList s))))
---                    liftIO $ putStrLn "--"
---                return ()
---            else do
---                return ()

---        liftIO $ putStrLn (printMove spec (Just s))
---        liftIO $ putStrLn (printTree spec gt)
    return ()


learnWinning :: CompiledSpec -> Player -> [Assignment] -> GameTree -> SolverT ()
learnWinning spec player s gt@(gtUnsetNodes -> []) = do
    -- Learn from the root of the tree
    found <- interpolateTree spec player [s] (gtExtend gt)
    dbgOutNoLearning spec player s gt found
    return ()
learnWinning spec player s (gtUnsetNodes -> gt:[]) = do
    -- Try to learn bad moves from the suffix
    learnBadMoves spec player gt

    -- Learn from the highest node under the fixed prefix
    core <- getLosingStates spec player gt
    case core of
        (Just c) -> do
            if (not (null c))
                then do
---                    coreExps    <- liftE $ mapM (assignmentToExpression 0) c
---                    allCores    <- liftE $ disjunct coreExps
                    found <- interpolateTree spec player c (gtExtend (gtRebase 0 gt))
                    dbgOutNoLearning spec player s gt found
                    return ()
                else do
                    liftIO $ putStrLn "empty core"
                    return ()
        Nothing -> do
---            liftIO $ putStrLn $ "lost in prefix"
            liftLog $ logLostInPrefix
            -- Can't find a core, so we must have lost in the prefix
            return ()
learnWinning spec player s gt = do
    liftIO $ putStrLn (printTree spec gt)
    throwError "Found more than one unset node in learnWinning"

interpolateTree :: CompiledSpec -> Player -> [[Assignment]] -> GameTree -> SolverT Bool
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
                throwError "Interpolation failed"
            else do
                let cube'   = map (filter (((==) StateVar) . assignmentSection)) (fromJust (interpolant ir))
                let cube''  = filter (all (\a -> assignmentRank a == gtRank gtB)) cube'
                let cube    = map (sort . map (\a -> setAssignmentRankCopy a 0 0)) cube''
                
---                liftIO $ putStrLn $ "--Losing for " ++ show player ++ " " ++ (show (gtBaseRank gtB)) ++ "--"
---                liftIO $ mapM (putStrLn . printMove spec . Just) cube
---                liftIO $ putStrLn $ "--Losing for " ++ show player ++ "--"
---                liftIO $ putStrLn ""
---                liftIO $ mapM (\c -> putStrLn $ "learnWinning " ++ show c) cube

                liftLog $ mapM logLosingState cube''

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
                return True
    else return False

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

verify :: Player -> CompiledSpec -> [Assignment] -> Shortening -> GameTree -> GameTree -> SolverT (Maybe GameTree)
verify player spec s short gt cand = do
    let og = projectMoves gt cand
    when (not (isJust og)) $ throwError $ "Error projecting, moves didn't match\n" ++ show player ++ printTree spec gt ++ printTree spec cand
    let leaves = map appendChild $ filter (not . gtAtBottom) (map makePathTree (gtLeaves (fromJust og)))
    let leaves' = if opponent player == Universal
        then filter (not . gtLostInPrefix . gtRoot) leaves
        else leaves
    mapMUntilJust (verifyLoop (opponent player) spec s short) (zip [0..] leaves')

verifyLoop :: Player -> CompiledSpec -> [Assignment] -> Shortening -> (Int, GameTree) -> SolverT (Maybe GameTree)
verifyLoop player spec s short (i, gt) = do
    liftLog $ logVerify i
    r <- solveAbstract player spec s gt short
    return (fmap snd r)

refine gt cex = return $ appendNextMove gt cex

wipeTree gt = gtSetChildren (f gt) (map wipeTree (gtChildren gt))
    where
        f t@(gtPlayer -> Universal)   = gtSetExWins t Nothing
        f t@(gtPlayer -> Existential) = t

setMoves player spec model ogt = do
    let gt      = wipeTree (gtRoot ogt)
    let f       = if player == gtFirstPlayer gt then setMovesPlayer else setMovesOpp 
    cs          <- mapM (f player spec model) (gtChildren gt)
    let gt'     = gtSetChildren gt cs
    init        <- getVarsAtRank StateVar model 0 (gtBaseRank gt)
    return      $ gtSetInit init gt'

setMovesPlayer player spec model gt = do
    let vars    = if player == Existential then ContVar else UContVar
    move        <- getVarsAtRank vars model (gtCopyId gt) (gtRank gt)

    gt'         <- case player of
        Universal   -> do
            state   <- getVarsAtRank StateVar model (gtCopyId gt) (gtRank gt - 1)
            let gt' = gtSetExWins gt Nothing
            return $ gtSetMove (gtSetState gt' state) move
        Existential -> 
            return $ gtSetMove gt move

    cs          <- mapM (setMovesOpp player spec model) (gtChildren gt')
    return      $ gtSetChildren gt' cs

setMovesOpp player spec model gt = do
    gt' <- if opponent player == Universal
        then do
            let pCopy   = gtCopyId gt
            let goal    = goalFor Existential spec (gtRank gt - 1)
            cg          <- liftE $ getCached (gtRank gt - 1) pCopy pCopy pCopy (exprIndex goal)
            let exwinGt = if (isJust cg)
                then gtSetExWins gt (Just ((model !! ((exprIndex (fromJust cg)) - 1)) > 0))
                else gt
            state       <- getVarsAtRank StateVar model pCopy (gtRank gt - 1)
            return $ gtSetState exwinGt state
        else return gt
    let vars    = if opponent player == Existential then ContVar else UContVar
    move        <- getVarsAtRank vars model (gtCopyId gt) (gtRank gt)
    let gtm     = gtMove gt
    cs          <- mapM (setMovesPlayer player spec model) (gtChildren gt')
    return      $ gtSetChildren gt' cs

eqMoves xs ys = all id $ map (uncurry eqAssignments) $ zip xs ys
    where
    eqAssignments (Assignment s1 v1) (Assignment s2 v2) = s1 == s2 && eqVars v1 v2
    eqVars v1 v2 = v1 {ecopy = 0} == v2 {ecopy = 0}

getVarsAtRank sect model cpy rnk = do
    vars <- liftE $ getVars sect rnk cpy
    let as = Map.mapWithKey (\i v -> makeAssignment (model !! (i-1), v)) vars
    return $ Map.elems as

getConflicts vars conflicts cpy rnk = do
    let vs  = map (\v -> v {rank = rnk, ecopy = cpy}) vars
    ve      <- liftE $ mapM lookupVar vs
    let vd  = zip (map exprIndex (catMaybes ve)) vs
    let cs  = map (\c -> (abs c, c)) conflicts
    let as  = map ((uncurry liftMFst) . mapFst (\i -> lookup i cs)) vd
    return  $ map makeAssignment (catMaybes as)

shortEx ShortenExistential  = True
shortEx ShortenBoth         = True
shortEx _                   = False

shortUn ShortenUniversal    = True
shortUn ShortenBoth         = True
shortUn _                   = False

shortenStrategy :: Shortening -> Player -> CompiledSpec -> [Assignment] -> GameTree -> Expression -> Maybe [Int] -> [[Expression]] -> SolverT (Maybe [Int])
shortenStrategy (shortEx -> True) Existential spec s gt fml model es = do
    let reversedEs  = map reverse es
    (_, m')         <- foldlM (shortenLeaf gt) (fml, model) reversedEs
    return m'
shortenStrategy (shortUn -> True) Universal spec s gt _ model _ = do
    (es, f, gt')    <- makeFml spec Universal s gt True True
    return model
    let reversedEs  = map reverse es
    (_, m')         <- foldlM (shortenLeaf gt') (f, model) reversedEs
    return m'
shortenStrategy _ _ _ _ _ _ model _ = return model

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

learnBadMoves :: CompiledSpec -> Player -> GameTree -> SolverT ()
learnBadMoves spec player gt = do
    ls              <- get
    let allMoves    = filter (\(r, x, y) -> isJust x && isJust y) $ gtAllMovePairs gt
    let setTo0      = map (\a -> setAssignmentRankCopy a 1 0) . fromJust
    let allMoves'   = map (\(r, x, y) -> (r, setTo0 x, setTo0 y)) allMoves
    let unchecked   = Set.difference (Set.fromList allMoves') (checkedMoves ls)
    let playerMove  = if player == Existential then snd3 else thd3
    let mps         = filter (\m -> not (Set.member (playerMove m) (badMovesUn ls))) $ Set.toList unchecked
    fmls            <- mapM (uncurry3 (checkMoveFml spec player)) mps
    solved          <- mapM (mapSndM (satSolve 0 Nothing . fromJust)) $ filter (isJust . snd) (zip mps fmls)

    let badMoves    = map ((\x -> (fst3 x, playerMove x)) . fst) $ filter (not . satisfiable . snd) solved

    if player == Existential
    then do
        put $ ls { badMovesEx   = Set.union (badMovesEx ls) (Set.fromList badMoves)
                 , checkedMoves = Set.union (checkedMoves ls) unchecked }
    else do
        put $ ls { badMovesUn   = Set.union (badMovesUn ls) (Set.fromList (map snd badMoves))
                 , checkedMoves = Set.union (checkedMoves ls) unchecked }
