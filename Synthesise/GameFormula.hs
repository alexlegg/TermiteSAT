{-# LANGUAGE GADTs, RecordWildCards, ViewPatterns #-}
module Synthesise.GameFormula (
      makeFml
    , makeSplitFmls
    , makeInitCheckFml
    , makeUniversalWinCheckFml
    , goalFor
    ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List
import System.IO
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops

import Expression.Compile
import Expression.Expression
import Expression.AST
import Synthesise.GameTree
import Synthesise.SolverT
import Utils.Logger
import Utils.Utils
import qualified Data.Vector.Storable as SV

makeFml :: CompiledSpec -> Player -> [Assignment] -> GameTree -> Bool -> Bool -> SolverT ([[Expression]], Expression, GameTree)
makeFml spec player s ogt useBlocking unMustWin = do
    let gt      = normaliseCopies ogt
    let maxCopy = gtMaxCopy gt
    let root    = gtRoot gt
    let rank    = gtRank root
    let gtExt   = gtExtend gt

    liftE $ clearTempExpressions
    liftE $ initCopyMaps maxCopy

    filledTree <- (fmap gtRoot) $ fillTree player (head (gtChildren (gtRoot gtExt)))

    ls <- get
    let badMoves = if player == Universal then badMovesUn ls else badMovesEx ls

    -- Make a list of transitions, moves and blocking expressions to construct
    let cs      = gtSteps root
    let trans   = if null cs
                    then getTransitions rank root (Nothing, Nothing, Nothing)
                    else concatMap (getTransitions rank root) cs
    let goals   = getGoals rank maxCopy player
    let moves   = concatMap (getMoves rank player filledTree) (gtSteps filledTree)
    let cr      = gtCopiesAndRanks gt
    let bMoves  = concatMap (getBlockedMove cr) (Set.toList badMoves)
    block       <- if useBlocking
                    then getBlockedStates player cr
                    else return []
    unWinning   <- if unMustWin
                    then getUnWinningStates cr
                    else return []

    -- Construct everything in order
    exprs       <- mapM (construct spec player (gtFirstPlayer gt)) (sortConstructibles (trans ++ moves ++ goals ++ block ++ unWinning ++ bMoves))

    -- Construct init expression
    initMove    <- liftE $ moveToExpression (gtMaxCopy gt) (gtMove root)
    sExpr       <- liftE $ assignmentToExpression (gtMaxCopy gt) s
    let s'      = sExpr : catMaybes [initMove]
    
    -- Join transitions into steps and finally fml
    (es, fml)   <- case gtStepChildren root of
        []  -> do
            (es, step)  <- leafTo spec 0 maxCopy player rank 0
            return ([(Just (gtNodeId root), step) : es], step)
        scs -> do
            steps       <- mapM (makeSteps maxCopy rank spec player Nothing unMustWin root) scs
            step        <- liftE $ conjunctTemp maxCopy (map snd steps)
            return (map ((Just (gtNodeId root), step) :) (concatMap fst steps), step)

    let goal    = goalFor player spec rank
    cg          <- liftE $ getCached rank 0 0 0 (exprIndex goal)
    when (isNothing cg) $ throwError "Max rank goal not created in advance"

    fml' <- if player == Existential
        then do
            fmlOrGoal <- liftE $ disjunctTemp maxCopy [fromJust cg, fml]
            liftE $ conjunctTemp maxCopy (fmlOrGoal : s' ++ catMaybes exprs)
        else do
            fmlAndGoal <- liftE $ conjunctTemp maxCopy [fromJust cg, fml]
            liftE $ conjunctTemp maxCopy (fmlAndGoal : s' ++ catMaybes exprs)

    -- Gametree and expression bookkeeping
    let node2expr   = concatMap catMaybeFst es
    let gt'         = gtSetExprIds player (map (mapSnd exprIndex) node2expr) root

    return (map (map snd) es, fml', gt')

isBlockingConstruct CBlocked{..}    = True
isBlockingConstruct _               = False

makeSplitFmls :: CompiledSpec -> Player -> [[Assignment]] -> GameTree -> SolverT (Maybe (GameTree, GameTree, Expression, Expression))
makeSplitFmls _ _ _ (gtEmpty -> True)       = return Nothing
makeSplitFmls _ _ _ (gtIsPrefix -> True)    = return Nothing
makeSplitFmls spec player s gt = do
    --Assume GT already normalised
    let maxCopy     = gtMaxCopy gt
    let root        = gtRoot gt
    let rank        = gtRank root
    let (t1, t2')   = gtSplit player gt
    let t2          = head (gtChildren t2')

    let nRank   = gtRank t2
    let nCopy   = gtCopyId (gtRoot t2)
    let pCopy   = gtCopyId (gtRoot t2)
    let copy1   = gtCopyId t2
    let copy2   = gtCopyId (head (gtChildren t2))

    liftE $ clearTempExpressions
    liftE $ initCopyMaps maxCopy

    constA <- liftM (zip (repeat True)) $ getConstructsFor spec maxCopy t1 player (Just (nRank-1, copy2))
    constB <- liftM (zip (repeat False)) $ getConstructsFor spec maxCopy t2 player Nothing
    let sorted = sortBy (\x y -> compare (sortIndex (snd x)) (sortIndex (snd y))) (constA ++ constB)

    -- Construct everything in order
    exprs       <- mapM (mapSndM (construct spec player (gtFirstPlayer gt))) sorted
    let exprsA  = catMaybes $ map snd (filter fst exprs)
    let exprsB  = catMaybes $ map snd (filter (not . fst) exprs)
    
    -- Construct init expression
    initMove    <- liftE $ moveToExpression maxCopy (gtMove root)
    ss          <- liftE $ mapM (assignmentToExpression 0) s
    let s'      = ss ++ catMaybes [initMove]

    -- Join transitions into steps and finally fml
    fmlA' <- case gtStepChildren (gtRoot t1) of
        []  -> do
            liftE $ trueExpr
        scs -> do
            steps <- mapM (makeSteps maxCopy (gtRank (gtRoot t1)) spec player (Just (nRank, pCopy)) False (gtRoot t1)) scs
            liftE $ conjunctTemp maxCopy (map snd steps)

    fmlA        <- liftE $ conjunctTemp maxCopy (fmlA' : s' ++ exprsA)

    stepB       <- liftE $ getCached nRank pCopy copy1 copy2 (exprIndex ((t spec) !! (nRank-1)))
    let goalB   = goalFor player spec nRank
    let goalB'  = goalFor player spec (nRank - 1)
    cg          <- liftE $ getCached nRank pCopy pCopy pCopy (exprIndex goalB)
    cg'         <- liftE $ getCached (nRank - 1) copy2 copy2 copy2 (exprIndex goalB')

    when (isNothing stepB) $ throwError $ "Transition was not created in advance for fmlB"
    when (isNothing cg) $ throwError $ "Goal was not created in advance: " ++ show (nRank, nCopy)
    when (isNothing cg') $ throwError $ "Goal was not created in advance: " ++ show (nRank-1, nCopy)

    -- If gtB is the final step then we must end up in the goal
    -- Otherwise the only requirement is that there exists a valid
    -- transition that keeps us inside winningMay
    fmlB'       <- case nRank of
                    1   -> liftE $ conjunctTemp maxCopy (fromJust stepB : fromJust cg' : exprsB)
                    _   -> liftE $ conjunctTemp maxCopy (fromJust stepB : exprsB)
    fmlB        <- case player of
                    Existential -> liftE $ disjunctTemp maxCopy [fromJust cg, fmlB']
                    Universal   -> liftE $ conjunctTemp maxCopy [fromJust cg, fmlB']

    return (Just (t1, t2, fmlA, fmlB))

makeInitCheckFml :: Int -> [Assignment] -> [[Assignment]] -> Expression -> SolverT Expression
makeInitCheckFml rank init must goal = do
    liftE $ clearTempExpressions
    liftE $ initCopyMaps 0

    let must'   = map (map (\a -> setAssignmentRankCopy a rank 0)) must
    let init'   = map (\a -> setAssignmentRankCopy a rank 0) init
    g'          <- liftE $ setRank rank goal
    ms          <- liftE $ mapM (assignmentToExpression 0) must'
    d           <- liftE $ disjunctC 0 (g' : ms)
    i           <- liftE $ assignmentToExpression 0 init'
    liftE $ conjunctC 0 [d, i]

makeUniversalWinCheckFml :: [[Assignment]] -> [[Assignment]] -> SolverT Expression
makeUniversalWinCheckFml wm1 wm2 = do
    liftE $ clearTempExpressions
    liftE $ initCopyMaps 0

    wm1' <- liftE $ mapM (assignmentToExpression 0) wm1
    wm2' <- liftE $ mapM (assignmentToExpression 0) wm2

    wm1'' <- liftE $ disjunct wm1'
    wm2'' <- liftE $ disjunct wm2'

    e <- liftE $ equate wm1'' wm2''
---    ep <- liftE $ printExpression e
---    liftIO $ writeFile "checkUnWin" ep
    liftE $ negation e

data Construct where
    CTransition :: {
          ctRank        :: Int
        , ctParentCopy  :: Int
        , ctCopy1       :: Int
        , ctCopy2       :: Int
    } -> Construct
    CMove :: {
          cmRank         :: Int
        , cmParentCopy   :: Int
        , cmCopy         :: Int
        , cmPlayer       :: Player
        , cmAssignment   :: [Assignment]
    } -> Construct
    CGoal :: {
          cgRank        :: Int
        , cgCopy        :: Int
        , cgPlayer      :: Player
    } -> Construct
    CBlocked :: {
          cbRank        :: Int
        , cbCopy        :: Int
        , cbAssignment  :: [Assignment]
    } -> Construct
    CUnWinning :: {
          cuRank        :: Int
        , cuCopy        :: Int
        , cuAssignment  :: [Assignment]
    } -> Construct
    CBlockMove :: {
          cbmRank       :: Int
        , cbmCopy       :: Int
        , cbmState      :: [Assignment]
        , cbmMove       :: [Assignment]
    } -> Construct
    deriving (Show)

sortIndex :: Construct -> Int
sortIndex CTransition{..}   = maximum [ctParentCopy, ctCopy1, ctCopy2]
sortIndex CMove{..}         = cmCopy
sortIndex CBlocked{..}      = cbCopy
sortIndex CGoal{..}         = cgCopy
sortIndex CUnWinning{..}    = cuCopy
sortIndex CBlockMove{..}    = cbmCopy

construct :: CompiledSpec -> Player -> Player -> Construct -> SolverT (Maybe Expression)
construct s p f t@CTransition{} = makeTransition s f t
construct s p f m@CMove{}       = makeMove s p m
construct s p f b@CBlocked{}    = blockExpression b
construct s p f g@CGoal{}       = makeGoal s p g
construct s p f u@CUnWinning{}  = makeUnWinning u
construct s p f bm@CBlockMove{} = makeBlockedMove bm

sortConstructibles :: [Construct] -> [Construct]
sortConstructibles = sortBy (\x y -> compare (sortIndex x) (sortIndex y))

getConstructsFor :: CompiledSpec -> Int -> GameTree -> Player -> Maybe (Int, Int) -> SolverT [Construct]
getConstructsFor spec maxCopy gt player stopAt = do
    let root    = gtRoot gt
    let rank    = gtRank root
    let cs      = gtSteps root

    let trans   = if null cs
                    then getTransitions rank root (Nothing, Nothing, Nothing)
                    else concatMap (getTransitions rank root) cs
    let goals   = getGoals rank maxCopy player
    moves       <- if (gtEmpty root)
        then return []
        else do
            filledTree <- (fmap gtRoot) $ fillTree player (head (gtChildren root))
            return $ concatMap (getMoves rank player filledTree) (gtSteps filledTree)
    let cr      = case stopAt of
                Just (stopRank, stopCopy)   -> filter (\(c, r) -> not (r <= stopRank && c == stopCopy)) (gtCopiesAndRanks gt)
                Nothing                     -> [(gtCopyId root, rank), (gtCopyId (head (gtChildren gt)), rank-1)]
    block'      <- getBlockedStates player cr
    let block   = case stopAt of
                Just (stopRank, stopCopy)   -> filter (\b -> not (cbRank b <= stopRank && cbCopy b == stopCopy)) block'
                Nothing                     -> block'
    return $ trans ++ goals ++ moves ++ block

getMoves :: Int -> Player -> GameTree -> (Move, Move, Maybe GameTree) -> [Construct]
getMoves rank player gt (m1, m2, c) = m1' ++ m2' ++ next
    where
        m1'         = maybe [] (\m -> [CMove rank parentCopy copy1 first m]) m1
        m2'         = maybe [] (\m -> [CMove rank parentCopy copy2 (opponent first) m]) m2
        parentCopy  = gtCopyId gt 
        copy1       = maybe parentCopy (gtCopyId . gtParent) c
        copy2       = maybe copy1 gtCopyId c
        first       = gtFirstPlayer gt
        next        = if isJust c && rank >= 1
            then concatMap (getMoves (rank-1) player (fromJust c)) (gtSteps (fromJust c))
            else []

getTransitions :: Int -> GameTree -> (Move, Move, Maybe GameTree) -> [Construct]
getTransitions rank gt (_, _, c) = (CTransition rank parentCopy copy1 copy2) : next
    where
        parentCopy  = gtCopyId gt 
        copy1       = maybe parentCopy (gtCopyId . gtParent) c
        copy2       = maybe copy1 gtCopyId c
        next        = if isJust c && rank >= 1
            then case gtSteps (fromJust c) of
                []  -> map (\x -> CTransition x copy2 copy2 copy2) (reverse [1..(rank-1)])
                cs  -> concatMap (getTransitions (rank-1) (fromJust c)) cs
            else map (\x -> CTransition x copy2 copy2 copy2) (reverse [1..(rank-1)])

sortTransitions :: [(Int, Int, Int, Int)] -> [(Int, Int, Int, Int)]
sortTransitions = sortBy f
    where f (_, x1, y1, z1) (_, x2, y2, z2) = compare (maximum [x1, y1, z1]) (maximum [x2, y2, z2])

getGoals :: Int -> Int -> Player -> [Construct]
getGoals rank mc p = map (\(r, c) -> CGoal r c p) [(r, c) | r <- [0..rank], c <- [0..mc]]

makeGoal :: CompiledSpec -> Player -> Construct -> SolverT (Maybe Expression)
makeGoal spec player CGoal{..} = do
    let g   = goalFor player spec cgRank
    cached  <- liftE $ getCached cgRank cgCopy cgCopy cgCopy (exprIndex g)
    when (isNothing cached) $ do
---        liftIO $ putStrLn "make goal"
        cg      <- liftE $ setCopy (Map.singleton (StateVar, cgRank) cgCopy) g
        liftE $ cacheStep cgRank cgCopy cgCopy cgCopy (exprIndex g) cg
    return Nothing

getBlockedStates :: Player -> [(Int, Int)] -> SolverT [Construct]
getBlockedStates Existential copyRanks = do
    LearnedStates{..} <- get
    return $ concatMap (\(c, r) -> blockAtRank winningMay r c) copyRanks
    where
        blockAtRank block r c = map (CBlocked r c) (map Set.toList (maybe [] Set.toList (Map.lookup r block)))
getBlockedStates Universal copyRanks = do
    LearnedStates{..} <- get
    return [CBlocked r c a | (c, r) <- copyRanks, a <- (map Set.toList (Set.toList winningMust))]

getUnWinningStates :: [(Int, Int)] -> SolverT [Construct]
getUnWinningStates copyRanks = do
    LearnedStates{..} <- get
    return $ concatMap (\(c, r) -> winAtRank winningMay r c) copyRanks
    where
        winAtRank block r c = map (CUnWinning r c) (map Set.toList (maybe [] Set.toList (Map.lookup r block)))

getBlockedMove :: [(Int, Int)] -> (Move, Move) -> [Construct]
getBlockedMove copyRanks (state, move) = map makeCBlockMove copyRanks
    where
        makeCBlockMove (c, r) = CBlockMove {   cbmRank     = r
                                          , cbmCopy     = c
                                          , cbmState    = fromJust state
                                          , cbmMove     = fromJust move }

makeBlockedMove CBlockMove{..} = do
    let ss = map (\a -> setAssignmentRankCopy a cbmRank cbmCopy) cbmState
    let ms = map (\a -> setAssignmentRankCopy a cbmRank cbmCopy) cbmMove
    state   <- liftE $ assignmentToExpression cbmCopy ss
    move    <- liftE $ assignmentToExpression cbmCopy ms
    moven   <- liftE $ negationC cbmCopy move
    e       <- liftE $ implicateC cbmCopy state moven
    return (Just e)

blockExpression CBlocked{..} = do
    let as = map (\a -> setAssignmentRankCopy a cbRank cbCopy) cbAssignment
    cached <- liftE $ getCachedMove cbCopy (BlockedState, as)
    case cached of
        (Just b)    -> return (Just b)
        Nothing     -> do
---            liftIO $ putStrLn "make Blocking expression"
            b <- liftE $ blockAssignment cbCopy as
            liftE $ cacheMove cbCopy (BlockedState, as) b
            return (Just b)

makeUnWinning CUnWinning{..} = do
    let as = map (\a -> setAssignmentRankCopy a cuRank cuCopy) cuAssignment
    cached <- liftE $ getCachedMove cuCopy (UnWinState, as)
    when (isNothing cached) $ do 
        b <- liftE $ assignmentToExpression cuCopy as
        liftE $ cacheMove cuCopy (UnWinState, as) b
    return Nothing

makeTransition :: CompiledSpec -> Player -> Construct -> SolverT (Maybe Expression)
makeTransition spec first CTransition{..} = do
    let i                   = ctRank - 1
    let CompiledSpec{..}    = spec

    if ctRank > 0
    then do
        step <- liftE $ getCached ctRank ctParentCopy ctCopy1 ctCopy2 (exprIndex (t !! i))

        when (not (isJust step)) $ do
---            liftIO $ putStrLn "make new step"
---            liftIO $ putStrLn (show (ctRank, ctParentCopy, ctCopy1, ctCopy2))
            step <- if ctCopy1 == 0 && ctCopy2 == 0 && ctParentCopy == 0
                then return (t !! i)
                else do
                    let cMap = Map.fromList [
                                  ((playerToSection first, ctRank), ctCopy1)
                                , ((playerToSection (opponent first), ctRank), ctCopy2)
                                , ((StateVar, ctRank-1), ctCopy2)
                                , ((StateVar, ctRank), ctParentCopy)
                                ]
                    liftE $ setCopy cMap (t !! i)
            liftE $ cacheStep ctRank ctParentCopy ctCopy1 ctCopy2 (exprIndex (t !! i)) step

        return Nothing
    else do
        return Nothing

makeSteps :: Int -> Int -> CompiledSpec -> Player -> Maybe (Int, Int) -> Bool -> GameTree -> GameTree -> SolverT ([[(Maybe Int, Expression)]], Expression)
makeSteps maxCopy rank spec player extend unMustWin gt c = do
    let parentCopy          = gtCopyId gt 
    let copy1               = gtCopyId (gtParent c)
    let copy2               = gtCopyId c

    (es, next) <- case gtStepChildren c of
        [] -> do
            if isJust extend && rank /= 1 -- == Just (rank-1, copy2)
            then return ([], Nothing)
            else do
                (es, step) <- leafTo spec copy2 maxCopy player (rank-1) 0
                return ([(Just (gtNodeId c), step) : es], Just step)
        cs -> do
            steps <- mapM (makeSteps maxCopy (rank-1) spec player extend unMustWin c) cs
            conj <- liftE $ conjunctTemp maxCopy (map snd steps)
            return (map ((Just (gtNodeId c), conj) :) (concatMap fst steps), Just conj)

    s <- singleStep spec rank maxCopy player parentCopy copy1 copy2 next unMustWin
    return (es, s)

makeMove :: CompiledSpec -> Player -> Construct -> SolverT (Maybe Expression)
makeMove spec player CMove{..} = do
    let CompiledSpec{..}    = spec
    let vh                  = if cmPlayer == Universal then vu else vc
    let i                   = cmRank - 1
    let isHatMove           = player /= cmPlayer && useFair
    let moveType            = (if isHatMove then HatMove else RegularMove) cmParentCopy

    cached <- liftE $ getCachedMove cmCopy (moveType, cmAssignment)
    case cached of
        (Just m)    -> return (Just m)
        Nothing     -> do
---            liftIO $ putStrLn "makeMove"
            move <- if isHatMove
                then liftE $ makeHatMove cmCopy (vh !! i) cmAssignment
                else liftE $ assignmentToExpression cmCopy cmAssignment

            let cMap = Map.fromList [
                      ((playerToSection cmPlayer, cmRank), cmCopy)
                    , ((HatVar, cmRank), cmCopy)
                    , ((StateVar, cmRank), cmParentCopy)
                    ]

            mc <- liftE $ setCopy cMap move
            liftE $ cacheMove cmCopy (moveType, cmAssignment) mc

            return (Just mc)

makeHatMove c valid m = do
    move        <- assignmentToExpression c m
    move_hat    <- setHatVar c move
    vp <- printExpression valid
    valid_hat   <- setHatVar c valid
    imp         <- implicateC c valid_hat move
    conjunctC c [move_hat, imp]

singleStep spec rank maxCopy player parentCopy copy1 copy2 next unMustWin = do
    let i                   = rank - 1
    let CompiledSpec{..}    = spec

    step <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex (t !! i))
    when (isNothing step) $ throwError $ "Transition was not created in advance: " ++ show (rank, parentCopy, copy1, copy2)

    let goal    = goalFor player spec i
    cg          <- liftE $ getCached i copy2 copy2 copy2 (exprIndex goal)
    when (isNothing cg) $ throwError $ "Goal was not created in advance: " ++ show (i, copy2)

    unWins <- if unMustWin 
        then do
            ws          <- getUnWinningStates [(copy2, rank)]
            let as      = map (map (\a -> setAssignmentRankCopy a rank copy2) . cuAssignment) ws
            ws'         <- liftE $ mapM (\as -> getCachedMove copy2 (UnWinState, as)) as
            when (any isNothing ws') $ throwError "Universal winning state not created in advance"
            d           <- liftE $ disjunctTemp maxCopy (catMaybes ws')
            f           <- liftE $ falseExpr
            if (null ws) then return (Just f) else return (Just d)
        else return Nothing

    let g = if unMustWin then unWins else cg
    joinNext maxCopy player unMustWin (fromJust g) (fromJust step) next
---    case next of
---        Nothing -> return $ fromJust step
---        Just n  -> do
---            goal <- if player == Existential
---                then liftE $ disjunctTemp maxCopy [n, fromJust cg]
---                else liftE $ conjunctTemp maxCopy [n, fromJust cg]

---            liftE $ conjunctTemp maxCopy [fromJust step, goal]

joinNext maxCopy player unMustWin goal step next
    | isNothing next                        = return step
    | player == Existential                 = do
        g <- liftE $ disjunctTemp maxCopy [fromJust next, goal]
        liftE $ conjunctTemp maxCopy [step, g]
    | player == Universal && not unMustWin  = do
        liftE $ conjunctTemp maxCopy [step, goal, fromJust next]
    | player == Universal && unMustWin      = do
        g <- liftE $ disjunctTemp maxCopy [fromJust next, goal]
        liftE $ conjunctTemp maxCopy [step, g]

moveToExpression mc Nothing    = return Nothing
moveToExpression mc (Just a)   = do
    e <- assignmentToExpression mc a
    return (Just e)

goalFor Existential spec i  = (cg spec) !! i
goalFor Universal spec i    = (ug spec) !! i

leafTo :: CompiledSpec -> Int -> Int -> Player -> Int -> Int -> SolverT ([(Maybe Int, Expression)], Expression)
leafTo spec copy maxCopy player rank rankTo = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1

    if rank == rankTo
    then do
        let g   = goalFor player spec rankTo
        cg      <- liftE $ getCached rank copy copy copy (exprIndex g)
        when (isNothing cg) $ throwError $ "Goal was not created in advance: " ++ show (rank, copy)
        return ([], fromJust cg)
    else do
        (es, next) <- leafTo spec copy maxCopy player (rank - 1) rankTo

        step <- singleStep spec rank maxCopy player copy copy copy (Just next) False
        return ((Nothing, step) : es, step)

playerToSection :: Player -> Section
playerToSection Existential = ContVar
playerToSection Universal   = UContVar

fillTree :: Player -> GameTree -> SolverT GameTree
fillTree player gt = do
    ls <- get
    if Map.null (defaultUnMoves ls) || Map.null (defaultExMoves ls)
    then return gt
    else do
        let moveMap = if player == Existential
            then defaultUnMoves ls
            else defaultExMoves ls

        let gt' = if gtPlayer gt == opponent player && isNothing (gtMove gt)
            then gtSetMove gt (fromJust (Map.lookup (gtRank gt) moveMap))
            else gt

        let cs = gtChildren gt'
        cs' <- mapM (fillTree player) cs

        return $ gtSetChildren gt' cs'
