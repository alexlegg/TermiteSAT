{-# LANGUAGE RecordWildCards, ViewPatterns #-}
module Synthesise.Solver (
      checkRank
    , checkInit
    , checkUniversalWin
    , LearnedStates(..)
    , LearningType(..)
    , emptyLearnedStates
    ) where

import Data.Maybe
import Data.List
import Data.Foldable (foldlM)
import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

import Expression.Compile
import Expression.Expression
import Synthesise.SolverT
import Synthesise.GameTree
import Synthesise.GameFormula
import Synthesise.Config
import SatSolver.SatSolver
import SatSolver.Interpolator
import Utils.Logger
import Utils.Utils

checkRank :: CompiledSpec -> Int -> [Assignment] -> Maybe ([[Assignment]], [[Assignment]]) -> Config -> SolverT (Int, Bool)
checkRank spec rnk s def config = do
    initDefaultMoves spec config rnk s def
    r <- solveAbstract Universal spec config s (gtNew Existential rnk) (shortening config)

    satTime             <- liftIO $ timeInSAT
    satCalls            <- liftIO $ totalSATCalls
    (intTime, eA, eB)   <- liftIO $ timeInInterpolate

    liftLog $ putStrLnDbg 1 "----------------"
    liftLog $ putStrLnDbg 1 $ "timeInSAT = " ++ (show (toSeconds satTime))
    liftLog $ putStrLnDbg 1 $ "SAT Calls = " ++ (show satCalls)
    liftLog $ putStrLnDbg 1 $ "timeInInterpolate = " ++ (show (toSeconds intTime))
    liftLog $ putStrLnDbg 1 $ "timeInEnodeA = " ++ (show (toSeconds eA))
    liftLog $ putStrLnDbg 1 $ "timeInEnodeB = " ++ (show (toSeconds eB))
    liftLog $ putStrLnDbg 1 "----------------"

    extraSatCalls <- if (isJust (initMin config) && isJust r && rnk <= fromJust (initMin config))
    then do
        let i       = fromJust (gtMove (gtRoot (fromJust r)))
        (cube, sc)  <- tryReducedInit spec rnk 0 [] i config 0
        let cube'   = map (sort . map (\a -> setAssignmentRankCopy a 0 0)) [cube]

        ls <- get
        put $ ls {
            winningMay = alterAll (insertIntoSet cube') [1..rnk] (winningMay ls)
        }

        return sc
    else return 0

    liftIO $ putStrLn "==================================================="

    ls <- get 
    let printSet = printMove spec . Just . sort . Set.toList
    let wMayStr = interMap "\n--\n" (\(_, wm) -> interMap "\n" printSet (Set.toList wm)) (Map.toList (winningMay ls))
    let wMustStr = interMap "\n" printSet (Set.toList (winningMust ls))
    liftLog $ logWinning wMayStr wMustStr
    
    liftLog (logRank rnk)

    return (satCalls + extraSatCalls, isNothing r)

tryReducedInit :: CompiledSpec -> Int -> Int -> [Assignment] -> [Assignment] -> Config -> Int -> SolverT ([Assignment], Int)
tryReducedInit _ _ _ cube [] _ sc               = return (cube, sc)
tryReducedInit spec rnk a cube (x:xs) config sc = do
    let s = cube ++ xs
    r <- solveAbstract Existential spec config s (appendChild (gtNew Existential rnk)) (shortening config)

    satTime             <- liftIO $ timeInSAT
    satCalls            <- liftIO $ totalSATCalls
    (intTime, eA, eB)   <- liftIO $ timeInInterpolate

    liftLog $ putStrLnDbg 2 "----------------"
    liftLog $ putStrLnDbg 2 "Expand Init"
    liftLog $ putStrLnDbg 2 (printMove spec (Just cube))
    liftLog $ putStrLnDbg 2 $ "timeInSAT = " ++ (show (toSeconds satTime))
    liftLog $ putStrLnDbg 2 $ "SAT Calls = " ++ (show satCalls)
    liftLog $ putStrLnDbg 2 $ "timeInInterpolate = " ++ (show (toSeconds intTime))
    liftLog $ putStrLnDbg 2 $ "timeInEnodeA = " ++ (show (toSeconds eA))
    liftLog $ putStrLnDbg 2 $ "timeInEnodeB = " ++ (show (toSeconds eB))
    liftLog $ putStrLnDbg 2 "----------------"

    liftLog (logRankAux (printMove spec (Just s)) (printMove spec (Just [x])) (isJust r) rnk a)

    if isJust r
        then tryReducedInit spec rnk (a+1) (cube ++ [x]) xs config (sc + satCalls)
        else tryReducedInit spec rnk (a+1) cube xs config (sc + satCalls)
    
initDefaultMoves :: CompiledSpec -> Config -> Int -> [Assignment] -> Maybe ([[Assignment]], [[Assignment]]) -> SolverT ()
initDefaultMoves _ _ rank _ (Just (uMoves, eMoves)) = do
    let defaultUn = zipWith (\r m -> (r, map (\a -> setAssignmentRankCopy a r 0) m)) [1..rank] uMoves
    let defaultEx = zipWith (\r m -> (r, map (\a -> setAssignmentRankCopy a r 0) m)) [1..rank] eMoves
    ls <- get
    put $ ls { defaultUnMoves   = Map.fromList defaultUn
             , defaultExMoves   = Map.fromList defaultEx }
initDefaultMoves spec config rank s Nothing = do
    case (moveLearning config) of
        MLDefaultMoves n -> do
            ls <- get
            put $ ls { defaultUnMoves   = Map.empty 
                     , defaultExMoves   = Map.empty }

            replicateM_ n $ do
                findDefaultMoves Existential spec rank s 
                findDefaultMoves Universal spec rank s 

            ls' <- get
            let uMoveStr = interMap "\n" (printMove spec . Just) (Map.elems (defaultUnMoves ls'))
            let eMoveStr = interMap "\n" (printMove spec . Just) (Map.elems (defaultExMoves ls'))
            liftLog $ logDefaultMoves (uMoveStr, eMoveStr)
        _ -> return ()

findDefaultMoves :: Player -> CompiledSpec -> Int -> [Assignment] -> SolverT ()
findDefaultMoves player spec rank s = do
    let gt = gtExtend (gtNew Existential rank)
    let pm = if (player == Existential) then ContVar else UContVar
    let pv = if (player == Existential) then (cont spec) else (ucont spec)

    let defaultMoves = if (player == Existential) then defaultExMoves else defaultUnMoves

    (_, f, _)   <- makeFml spec player s gt False
    r           <- satSolve (gtMaxCopy gt) Nothing f

    ls <- get
    dmoves <- if satisfiable r
        then do
            moves <- mapM (getVarsAtRank pm (fromJust (model r)) 0) [1..rank]
            return $ Map.fromList (zip [1..rank] moves)
        else do
            -- No way to win at this rank against opp default moves
            if Map.null (defaultMoves ls)
            then do
                let someMove = map (\v -> Assignment Pos v) pv
                return $ foldl (\m k -> Map.insert k someMove m) Map.empty [1..rank]
            else 
                return $ defaultMoves ls

    ls' <- get
    case player of
        Existential -> put $ ls' { defaultExMoves   = dmoves }
        Universal   -> put $ ls' { defaultUnMoves   = dmoves }

checkInit :: Int -> [Assignment] -> [[Assignment]] -> Expression -> SolverT Bool
checkInit k i must goal = do
    fml     <- makeInitCheckFml k i must goal
    r       <- satSolve 0 Nothing fml
    return $ satisfiable r

checkUniversalWin :: Int -> SolverT Bool
checkUniversalWin k = do
    ls <- get
    let wm1     = map (\i -> Map.lookup i (winningMay ls)) [1..k-1]
    let wm2     = map (\i -> Map.lookup i (winningMay ls)) [2..k-1]

    rs <- forM (zip wm1 wm2) $ \(wmA, wmB) -> do
        let f   = map Set.toList . maybe [] Set.toList
        fml     <- makeUniversalWinCheckFml (f wmA) (f wmB)
        r       <- satSolve 0 Nothing fml
        return r

    return $ any (not . satisfiable) rs

solveAbstract :: Player -> CompiledSpec -> Config -> [Assignment] -> GameTree -> Shortening -> SolverT (Maybe GameTree)
solveAbstract player spec config s gt short = do
    liftLog $ logSolve gt player []

    cand <- findCandidate player spec s short gt

    res <- refinementLoop player spec config s short cand gt gt

    liftLog $ logSolveComplete res
    liftLog $ logDumpLog

    return res

refinementLoop :: Player -> CompiledSpec -> Config -> [Assignment] -> Shortening -> Maybe GameTree -> GameTree -> GameTree -> SolverT (Maybe GameTree)
refinementLoop _ _ _ _ _ Nothing _ _                                = return Nothing
refinementLoop player spec config s short (Just cand) origGT absGT  = do
    v <- verify player spec config s short origGT cand
    case v of
        (Just cex) -> do
            let absGT' = appendNextMove absGT cex
            liftLog $ logRefine
            cand' <- solveAbstract player spec config s absGT' short
            refinementLoop player spec config s short cand' origGT absGT'
        Nothing -> do
            return (Just cand)
    

findCandidate :: Player -> CompiledSpec -> [Assignment] -> Shortening -> GameTree -> SolverT (Maybe GameTree)
findCandidate player spec s short gt = do
    (es, f, gt')    <- makeFml spec player s gt False
    res             <- satSolve (gtMaxCopy gt') Nothing f

    if satisfiable res
    then do
        (Just m)    <- shortenStrategy short player spec s gt' f (model res) es
        cand        <- setMoves player spec m (gtRoot gt')

        -- Generate a tree for the entire trace for the debug output
        outGt'      <- setMoves player spec m (gtRoot (gtExtend gt'))
        liftLog $ logCandidate (Just outGt')

        return (Just cand)
    else do
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

    (_, f, gt)      <- makeFml spec player [] gt' False
    cores           <- minimiseCore (gtMaxCopy gt) (Just s) f

    when (isJust cores) $ do
        cs          <- mapM (\core -> getConflicts (svars spec) core 0 rank) (fromJust cores)
        let cube    = map (sort . map (\a -> setAssignmentRankCopy a 0 0)) cs

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

    (_, f, gt)      <- makeFml spec player [] gt' False
    cores           <- minimiseCore (gtMaxCopy gt) (Just s) f

    if (isJust cores)
    then do
        cs <- mapM (\core -> getConflicts (svars spec) core 0 rank) (fromJust cores)
        return $ Just cs
    else 
        return Nothing

learnWinning :: CompiledSpec -> Player -> [Assignment] -> GameTree -> SolverT ()
learnWinning spec player s gt@(gtUnsetNodes -> []) = do
    -- Learn from the root of the tree
    interpolateTree spec player [s] True (gtExtend gt)
learnWinning spec player _ (gtUnsetNodes -> gt:[]) = do
    -- Learn from the highest node under the fixed prefix
    core <- getLosingStates spec player gt
    case core of
        Just [] -> liftIO $ putStrLn "empty core"
        Just c  -> interpolateTree spec player c True (gtExtend (gtRebase 0 gt))
        Nothing -> do
            -- Can't find a core, so we must have lost in the prefix
            liftLog $ logLostInPrefix
learnWinning spec _ _ gt = do
    liftIO $ putStrLn (printTree spec gt)
    throwError "Found more than one unset node in learnWinning"

interpolateTree :: CompiledSpec -> Player -> [[Assignment]] -> Bool -> GameTree -> SolverT ()
interpolateTree spec player s useDefault gt' = do
    let gt = normaliseCopies gt'
    fmls <- makeSplitFmls spec player s useDefault gt
    when (isJust fmls) $ do
        let Just (gtA, gtB, fmlA, fmlB) = fmls

        let vRank   = gtRank gtB
        let vCopy   = gtCopyId (gtRoot gtB)
        let vars    = map (\v -> v {rank = vRank, ecopy = vCopy}) (svars spec)
        project     <- liftE $ mapM (fmap (exprIndex . fromJust) . lookupVar) vars

        rA <- satSolve (gtMaxCopy gt) Nothing fmlA

        if (not (satisfiable rA))
        then do
            -- We lose in the prefix, so just keep going
            interpolateTree spec player s useDefault gtA
        else do
            ir <- interpolate (gtMaxCopy gt) project fmlA fmlB
            if (not (success ir))
            then do
                liftIO $ putStrLn (show player)
                liftIO $ putStrLn (printTree spec gtA)
                liftIO $ putStrLn (printTree spec gtB)
                throwError "Interpolation failed"
            else do
                let cube'   = filter (any (((==) StateVar) . assignmentSection)) (fromJust (interpolant ir))
                let cube    = filter (all (\a -> assignmentRank a == gtRank gtB)) cube'
                
                liftLog $ mapM_ logLosingState cube

                when (any (\cs -> not $ all (\a -> assignmentRank a == assignmentRank (head cs)) cs) cube') $ do
                    throwError "Not all cubes of the same rank"

                when (any (\cs -> not $ all (\a -> assignmentCopy a == assignmentCopy (head cs)) cs) cube') $ do
                    throwError "Not all cubes of the same copy"

                minCube' <- forM cube $ \c -> do
                    cores   <- minimiseCore (gtMaxCopy gt) (Just c) fmlB
                    mapM (\core -> getConflicts (svars spec) core vCopy vRank) (fromJust cores)

                let minCube = map (map (sort . map (\a -> setAssignmentRankCopy a 0 0))) minCube'

                ls <- get
                if player == Existential
                then put $ ls {
                      winningMay    = alterAll (insertIntoSet (concat minCube)) [1..gtBaseRank gtB] (winningMay ls)
                    }
                else put $ ls {
                      winningMust   = foldl insertCube (winningMust ls) (concat minCube)
                    }

                interpolateTree spec player s useDefault gtA

alterAll :: Ord k => (Maybe a -> Maybe a) -> [k] -> Map.Map k a -> Map.Map k a
alterAll _ [] m     = m
alterAll f (k:ks) m = Map.alter f k (alterAll f ks m)

insertIntoSet :: Ord a => [[a]] -> Maybe (Set.Set (Set.Set a)) -> Maybe (Set.Set (Set.Set a))
insertIntoSet xs ss = Just $ foldl insertCube (fromMaybe Set.empty ss) xs

insertCube :: Ord a => Set.Set (Set.Set a) -> [a] -> Set.Set (Set.Set a)
insertCube ss x' = let x = Set.fromList x' in
    if isJust $ find (\s -> s `Set.isSubsetOf` x) ss
        then ss 
        else Set.insert x $ Set.filter (\s -> not (x `Set.isSubsetOf` s)) ss

verify :: Player -> CompiledSpec -> Config -> [Assignment] -> Shortening -> GameTree -> GameTree -> SolverT (Maybe GameTree)
verify player spec config s short gt cand = do
    let og = projectMoves gt cand
    when (not (isJust og)) $ throwError $ "Error projecting, moves didn't match\n" ++ show player ++ printTree spec gt ++ printTree spec cand
    let leaves = map appendChild $ filter (not . gtAtBottom) (map makePathTree (gtLeaves (fromJust og)))
    let leaves' = if opponent player == Universal
        then filter (not . gtLostInPrefix . gtRoot) leaves
        else leaves
    mapMUntilJust (verifyLoop (opponent player) spec config s short) (zip [0..] leaves')

verifyLoop :: Player -> CompiledSpec -> Config -> [Assignment] -> Shortening -> (Int, GameTree) -> SolverT (Maybe GameTree)
verifyLoop player spec config s short (i, gt) = do
    liftLog $ logVerify i
    solveAbstract player spec config s gt short

wipeTree :: GameTree -> GameTree
wipeTree gt = gtSetChildren (f gt) (map wipeTree (gtChildren gt))
    where
        f t@(gtPlayer -> Universal) = gtSetExWins t Nothing
        f t@(gtPlayer -> _)         = t

setMoves :: Player -> CompiledSpec -> [Int] -> GameTree -> SolverT GameTree
setMoves player spec model ogt = do
    let gt      = wipeTree (gtRoot ogt)
    let f       = if player == gtFirstPlayer gt then setMovesPlayer else setMovesOpp 
    cs          <- mapM (f player spec model) (gtChildren gt)
    let gt'     = gtSetChildren gt cs
    i           <- getVarsAtRank StateVar model 0 (gtBaseRank gt)
    return      $ gtSetInit i gt'

setMovesPlayer :: Player -> CompiledSpec -> [Int] -> GameTree -> SolverT GameTree
setMovesPlayer player spec model gt = do
    let vars    = if player == Existential then ContVar else UContVar
    move        <- getVarsAtRank vars model (gtCopyId gt) (gtRank gt)

    gt'         <- case player of
        Universal   -> do
            s       <- getVarsAtRank StateVar model (gtCopyId gt) (gtRank gt - 1)
            let gt' = gtSetExWins gt Nothing
            return $ gtSetMove (gtSetState gt' s) move
        Existential -> 
            return $ gtSetMove gt move

    cs          <- mapM (setMovesOpp player spec model) (gtChildren gt')
    return      $ gtSetChildren gt' cs

setMovesOpp :: Player -> CompiledSpec -> [Int] -> GameTree -> SolverT GameTree
setMovesOpp player spec model gt = do
    gt' <- if opponent player == Universal
        then do
            let pCopy   = gtCopyId gt
            let goal    = goalFor Existential spec (gtRank gt - 1)
            cg          <- liftE $ getCached (gtRank gt - 1) pCopy pCopy pCopy (exprIndex goal)
            let exwinGt = if (isJust cg)
                then gtSetExWins gt (Just ((model !! ((exprIndex (fromJust cg)) - 1)) > 0))
                else gt
            s           <- getVarsAtRank StateVar model pCopy (gtRank gt - 1)
            return $ gtSetState exwinGt s
        else return gt
    cs          <- mapM (setMovesPlayer player spec model) (gtChildren gt')
    return      $ gtSetChildren gt' cs

getVarsAtRank :: Section -> [Int] -> Int -> Int -> SolverT [Assignment]
getVarsAtRank sect model cpy rnk = do
    vars <- liftE $ getVars sect rnk cpy
    let as = Map.mapWithKey (\i v -> makeAssignment (model !! (i-1), v)) vars
    return $ Map.elems as

getConflicts :: [ExprVar] -> [Int] -> Int -> Int -> SolverT [Assignment]
getConflicts vars conflicts cpy rnk = do
    let vs  = map (\v -> v {rank = rnk, ecopy = cpy}) vars
    ve      <- liftE $ mapM lookupVar vs
    let vd  = zip (map exprIndex (catMaybes ve)) vs
    let cs  = map (\c -> (abs c, c)) conflicts
    let as  = map ((uncurry liftMFst) . mapFst (\i -> lookup i cs)) vd
    return  $ map makeAssignment (catMaybes as)

shortEx :: Shortening -> Bool
shortEx ShortenExistential  = True
shortEx ShortenBoth         = True
shortEx _                   = False

shortUn :: Shortening -> Bool
shortUn ShortenUniversal    = True
shortUn ShortenBoth         = True
shortUn _                   = False

shortenStrategy :: Shortening -> Player -> CompiledSpec -> [Assignment] -> GameTree -> Expression -> Maybe [Int] -> [[Expression]] -> SolverT (Maybe [Int])
shortenStrategy (shortEx -> True) Existential _ _ gt fml model es = do
    (_, m')         <- foldlM (shortenLeaf gt) (fml, model) (map reverse es)
    return m'
shortenStrategy (shortUn -> True) Universal spec s gt _ model _ = do
    (es, f, gt')    <- makeFml spec Universal s gt True
    (_, m')         <- foldlM (shortenLeaf gt') (f, model) (map reverse es)
    return m'
shortenStrategy _ _ _ _ _ _ model _ = return model

shortenLeaf :: GameTree -> (Expression, Maybe [Int]) -> [Expression] -> SolverT (Expression, Maybe [Int])
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
