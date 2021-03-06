{-# LANGUAGE GADTs, RecordWildCards, ViewPatterns #-}
module Synthesise.GameFormula (
      makeFml
    , makeSplitFmls
    , makeInitCheckFml
    , makeUniversalWinCheckFml
    , goalFor
    , checkMoveFml
    , fillTree
    ) where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.List
import Control.Monad.State

import Expression.Compile
import Expression.Expression
import Synthesise.GameTree
import Synthesise.SolverT
import Utils.Utils

makeFml :: CompiledSpec -> Player -> [Assignment] -> GameTree -> Bool -> SolverT ([[Expression]], Expression, GameTree)
makeFml spec player s ogt unMustWin = do
    let gt      = normaliseCopies ogt
    let maxCopy = gtMaxCopy gt
    let root    = gtRoot gt
    let rank    = gtRank root
    let gtExt   = gtExtend gt

    liftE $ clearTempExpressions
    liftE $ initCopyMaps maxCopy

    filledTree <- (fmap gtRoot) $ fillTree player (head (gtChildren (gtRoot gtExt)))


    -- Make a list of transitions, moves and blocking expressions to construct
    let cs      = gtSteps root
    let trans   = if null cs
                    then getTransitions rank root (Nothing, Nothing, Nothing)
                    else concatMap (getTransitions rank root) cs
    let goals   = getGoals rank maxCopy player
    let moves   = concatMap (getMoves rank player filledTree) (gtSteps filledTree)
    let cr      = gtCopiesAndRanks gt

    bMoves      <- getBlockedMoves player filledTree
    block       <- getBlockedStates player cr
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
    when (isNothing cg) $ throwError "makeFml: Max rank goal not created in advance"

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

makeSplitFmls :: CompiledSpec -> Player -> [[Assignment]] -> Bool -> GameTree -> SolverT (Maybe (GameTree, GameTree, Expression, Expression))
makeSplitFmls _ _ _ _ (gtEmpty -> True)       = return Nothing
makeSplitFmls _ _ _ _ (gtIsPrefix -> True)    = return Nothing
makeSplitFmls spec player s useDefault gt = do
    --Assume GT already normalised
    let maxCopy     = gtMaxCopy gt
    let root        = gtRoot gt
    let (t1, t2')   = gtSplit gt
    let t2          = head (gtChildren t2')

    let nRank   = gtRank t2
    let nCopy   = gtCopyId (gtRoot t2)
    let pCopy   = gtCopyId (gtRoot t2)
    let copy2s  = map gtCopyId (gtChildren t2)

    liftE $ clearTempExpressions
    liftE $ initCopyMaps maxCopy

    constA <- liftM (zip (repeat True)) $ getConstructsFor maxCopy t1 player useDefault (Just (nRank-1, copy2s))
    constB <- liftM (zip (repeat False)) $ getConstructsFor maxCopy t2 player useDefault Nothing
    let sorted = sortBy (\x y -> compare (sortIndex (snd x)) (sortIndex (snd y))) (constA ++ constB)

    -- Construct everything in order
    exprs       <- mapM (mapSndM (construct spec player (gtFirstPlayer gt))) sorted
    let exprsA  = catMaybes $ map snd (filter fst exprs)
    let exprsB  = catMaybes $ map snd (filter (not . fst) exprs)

    -- Construct init expression
    initMove    <- liftE $ moveToExpression maxCopy (gtMove root)
    ss          <- liftE $ mapM (assignmentToExpression maxCopy) s
    let s'      = ss ++ catMaybes [initMove]

    -- Join transitions into steps and finally fml
    fmlA' <- case gtStepChildren (gtRoot t1) of
        []  -> do
            bCons   <- getBlockedStates player [(pCopy, nRank)]
            block   <- mapM blockExpression bCons
            if null block
                then liftE trueExpr
                else liftE $ conjunctTemp maxCopy block
        scs -> do
            steps <- mapM (makeSteps maxCopy (gtRank (gtRoot t1)) spec player (Just (nRank, pCopy)) False (gtRoot t1)) scs
            liftE $ conjunctTemp maxCopy (map snd steps)

    fmlA        <- liftE $ conjunctTemp maxCopy (fmlA' : s' ++ exprsA)

    bsteps <- forM (gtStepChildren (gtRoot t2)) $ \c -> do
        let parentCopy          = gtCopyId (gtRoot t2)
        let copy1               = gtCopyId (gtParent c)
        let copy2               = gtCopyId c

        singleStep spec nRank maxCopy player parentCopy copy1 copy2 Nothing False

    stepB       <- liftE $ conjunctTemp maxCopy bsteps
---    stepB       <- liftE $ getCached nRank pCopy copy1 copy2 (exprIndex ((t spec) !! (nRank-1)))

    let goalB   = goalFor player spec nRank
    cg          <- liftE $ getCached nRank pCopy pCopy pCopy (exprIndex goalB)
    when (isNothing cg) $ throwError $ "makeSplitFmls: Goal was not created in advance: " ++ show (nRank, nCopy)

    let goalB'  = goalFor player spec (nRank - 1)
    cgs'        <- mapM (\c -> liftE $ getCached (nRank - 1) c c c (exprIndex goalB')) copy2s
    when (any isNothing cgs') $ throwError $ "makeSplitFmls: Goals not created in advance: " ++ show (nRank-1) ++ show copy2s
    cg'         <- liftE $ conjunctTemp maxCopy (map fromJust cgs')

    bCons       <- mapM (\c -> getBlockedStates player [(c, nRank-1)]) copy2s
    block       <- mapM blockExpression (concat bCons)

    -- If gtB is the final step then we must end up in the goal
    -- Otherwise the only requirement is that there exists a valid
    -- transition that keeps us inside winningMay
    fmlB'       <- case nRank of
                    1   -> liftE $ conjunctTemp maxCopy (stepB : cg' : exprsB ++ block)
                    _   -> liftE $ conjunctTemp maxCopy (stepB : exprsB ++ block)
    fmlB        <- case player of
                    Existential -> liftE $ disjunctTemp maxCopy [fromJust cg, fmlB']
                    Universal   -> liftE $ conjunctTemp maxCopy [fromJust cg, fmlB']

    return (Just (t1, t2, fmlA, fmlB))

makeInitCheckFml :: Int -> [Assignment] -> [[Assignment]] -> Expression -> SolverT Expression
makeInitCheckFml rank i must goal = do
    liftE $ clearTempExpressions
    liftE $ initCopyMaps 0

    let must'   = map (map (\a -> setAssignmentRankCopy a rank 0)) must
    let init0   = map (\a -> setAssignmentRankCopy a rank 0) i
    g'          <- liftE $ setRank rank goal
    ms          <- liftE $ mapM (assignmentToExpression 0) must'
    d           <- liftE $ disjunctC 0 (g' : ms)
    initExpr    <- liftE $ assignmentToExpression 0 init0
    liftE $ conjunctC 0 [d, initExpr]

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
construct s _ f t@CTransition{} = makeTransition s f t
construct s p _ m@CMove{}       = makeMove s p m
construct _ _ _ b@CBlocked{}    = makeBlockExpression b
construct s p _ g@CGoal{}       = makeGoal s p g
construct _ _ _ u@CUnWinning{}  = makeUnWinning u
construct _ _ _ bm@CBlockMove{} = makeBlockedMove bm

sortConstructibles :: [Construct] -> [Construct]
sortConstructibles = sortBy (\x y -> compare (sortIndex x) (sortIndex y))

getConstructsFor :: Int -> GameTree -> Player -> Bool -> Maybe (Int, [Int]) -> SolverT [Construct]
getConstructsFor maxCopy gt player useDefault stopAt = do
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
            filledTree <- if useDefault
                              then (fmap gtRoot) $ fillTree player (head (gtChildren root))
                              else return root
            return $ concatMap (getMoves rank player filledTree) (gtSteps filledTree)
    let cr      = case stopAt of
                Just (stopRank, stopCopy)   -> filter (\(c, r) -> not (r <= stopRank && c `elem` stopCopy)) (gtCopiesAndRanks gt)
                Nothing                     -> gtCopiesAndRanks gt ++ (map (\c -> (c, rank-1)) (nub (map fst (gtCopiesAndRanks gt))))
    block'      <- getBlockedStates player cr
    let block   = case stopAt of
                Just (stopRank, stopCopy)   -> filter (\b -> not (cbRank b <= stopRank && cbCopy b `elem` stopCopy)) block'
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

getGoals :: Int -> Int -> Player -> [Construct]
getGoals rank mc p = map (\(r, c) -> CGoal r c p) [(r, c) | r <- [0..rank], c <- [0..mc]]

makeGoal :: CompiledSpec -> Player -> Construct -> SolverT (Maybe Expression)
makeGoal spec player CGoal{..} = do
    let g   = goalFor player spec cgRank
    cached  <- liftE $ getCached cgRank cgCopy cgCopy cgCopy (exprIndex g)
    when (isNothing cached) $ do
        cg      <- liftE $ setCopy (Map.singleton (StateVar, cgRank) cgCopy) g
        liftE $ cacheStep cgRank cgCopy cgCopy cgCopy (exprIndex g) cg
    return Nothing
makeGoal _ _ _ = throwError "makeGoal error"

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

getBlockedMoves :: Player -> GameTree -> SolverT [Construct]
getBlockedMoves player gt = do
    ls <- get
    let moveMap = if player == Existential
        then defaultUnMoves ls
        else defaultExMoves ls

    if Map.null moveMap
        then return []
        else do
            let crMoves = gtCRMoves (opponent player) gt
            if player == Existential
                then return $ concatMap (getBlockedUnMove crMoves) (Set.toList (badMovesUn ls))
                else return $ concatMap (getBlockedExMove crMoves) (Set.toList (badMovesEx ls))

getBlockedUnMove :: [(Int, Int, Move)] -> [Assignment] -> [Construct]
getBlockedUnMove copyRanks move       = map makeCBlockMove crs
    where
        makeCBlockMove (c, r, _)    = CBlockMove { cbmRank     = r
                                                 , cbmCopy     = c
                                                 , cbmMove     = move }
        crs                         = filter (isNothing . thd3) copyRanks

getBlockedExMove :: [(Int, Int, Move)] -> (Int, [Assignment]) -> [Construct]
getBlockedExMove copyRanks (rank, move) = map makeCBlockMove crs
    where
        makeCBlockMove (c, r, _)        = CBlockMove { cbmRank     = r
                                                     , cbmCopy     = c
                                                     , cbmMove     = move }
        crs                             = filter ((==) rank . snd3) $ filter (isNothing . thd3) copyRanks

makeBlockedMove :: Construct -> SolverT (Maybe Expression)
makeBlockedMove CBlockMove{..} = do
    let ms = map (\a -> setAssignmentRankCopy a cbmRank cbmCopy) cbmMove
    move    <- liftE $ assignmentToExpression cbmCopy ms
    moven   <- liftE $ negationC cbmCopy move
    return (Just moven)
makeBlockedMove _ = throwError "makeBlockedMove error"

makeBlockExpression :: Construct -> SolverT (Maybe Expression)
makeBlockExpression CBlocked{..} = do
    let as = map (\a -> setAssignmentRankCopy a cbRank cbCopy) cbAssignment
    cached <- liftE $ getCachedMove cbCopy (BlockedState, as)
    case cached of
        Just _  -> return Nothing
        Nothing -> do
            b <- liftE $ blockAssignment cbCopy as
            liftE $ cacheMove cbCopy (BlockedState, as) b
            return Nothing
makeBlockExpression _ = throwError "makeBlockExpression error"

blockExpression :: Construct -> SolverT Expression
blockExpression CBlocked{..} = do
    let as = map (\a -> setAssignmentRankCopy a cbRank cbCopy) cbAssignment
    cached <- liftE $ getCachedMove cbCopy (BlockedState, as)
    when (isNothing cached) $ throwError $ "blockExpression: Blocked expression not cached " ++ (show (cbCopy, cbRank))
    return $ fromJust cached
blockExpression _ = throwError "blockExpression error"

makeUnWinning :: Construct -> SolverT (Maybe Expression)
makeUnWinning CUnWinning{..} = do
    let as = map (\a -> setAssignmentRankCopy a cuRank cuCopy) cuAssignment
    cached <- liftE $ getCachedMove cuCopy (UnWinState, as)
    when (isNothing cached) $ do 
        b <- liftE $ assignmentToExpression cuCopy as
        liftE $ cacheMove cuCopy (UnWinState, as) b
    return Nothing
makeUnWinning _ = throwError "makeUnWinning error"

makeTransition :: CompiledSpec -> Player -> Construct -> SolverT (Maybe Expression)
makeTransition spec first CTransition{..} = do
    let i                   = ctRank - 1
    let CompiledSpec{..}    = spec

    if ctRank > 0
    then do
        step <- liftE $ getCached ctRank ctParentCopy ctCopy1 ctCopy2 (exprIndex (t !! i))

        when (not (isJust step)) $ do
            s <- if ctCopy1 == 0 && ctCopy2 == 0 && ctParentCopy == 0
                then return (t !! i)
                else do
                    let cMap = Map.fromList [
                                  ((playerToSection first, ctRank), ctCopy1)
                                , ((playerToSection (opponent first), ctRank), ctCopy2)
                                , ((StateVar, ctRank-1), ctCopy2)
                                , ((StateVar, ctRank), ctParentCopy)
                                ]
                    liftE $ setCopy cMap (t !! i)
            liftE $ cacheStep ctRank ctParentCopy ctCopy1 ctCopy2 (exprIndex (t !! i)) s

        return Nothing
    else do
        return Nothing
makeTransition _ _ _ = throwError "makeTransition error"

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
makeMove _ _ _ = throwError "makeMove error"

makeHatMove :: MonadIO m => Int -> Expression -> [Assignment] -> ExpressionT m Expression
makeHatMove c valid m = do
    move        <- assignmentToExpression c m
    move_hat    <- setHatVar c move
    valid_hat   <- setHatVar c valid
    imp         <- implicateC c valid_hat move
    conjunctC c [move_hat, imp]

singleStep :: CompiledSpec -> Int -> Int -> Player -> Int -> Int -> Int -> Maybe Expression -> Bool -> SolverT Expression
singleStep spec rank maxCopy player parentCopy copy1 copy2 next unMustWin = do
    let i                   = rank - 1
    let CompiledSpec{..}    = spec

    step <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex (t !! i))
    when (isNothing step) $ throwError $ "singlestep: Transition was not created in advance: " ++ show (rank, parentCopy, copy1, copy2)

    let goal    = goalFor player spec i
    cachedGoal <- liftE $ getCached i copy2 copy2 copy2 (exprIndex goal)
    when (isNothing cachedGoal) $ throwError $ "singlestep: Goal was not created in advance: " ++ show (i, copy2)

    let bCRs    = (copy2, rank) : if (isNothing next && i /= 0) then [(copy2, rank-1)] else []
    bCons       <- getBlockedStates player bCRs
    block       <- mapM blockExpression bCons

    unWins <- if unMustWin 
        then do
            ws          <- getUnWinningStates [(copy2, rank)]
            let as      = map (map (\a -> setAssignmentRankCopy a rank copy2) . cuAssignment) ws
            ws'         <- liftE $ mapM (\a -> getCachedMove copy2 (UnWinState, a)) as
            when (any isNothing ws') $ throwError "singlestep: Universal winning state not created in advance"
            d           <- liftE $ disjunctTemp maxCopy (catMaybes ws')
            f           <- liftE $ falseExpr
            if (null ws) then return (Just f) else return (Just d)
        else return Nothing

    let g = if unMustWin then unWins else cachedGoal
    joinNext maxCopy player unMustWin (fromJust g) (fromJust step) next block

joinNext :: Int -> Player -> Bool -> Expression -> Expression -> Maybe Expression -> [Expression] -> SolverT Expression
joinNext maxCopy player unMustWin goal step next block
    | isNothing next                        = do
        liftE $ conjunctTemp maxCopy (step : block)
    | player == Existential                 = do
        g <- liftE $ disjunctTemp maxCopy [fromJust next, goal]
        liftE $ conjunctTemp maxCopy ([step, g] ++ block)
    | player == Universal && not unMustWin  = do
        liftE $ conjunctTemp maxCopy ([step, goal, fromJust next] ++ block)
    | player == Universal && unMustWin      = do
        g <- liftE $ disjunctTemp maxCopy [fromJust next, goal]
        liftE $ conjunctTemp maxCopy ([step, g] ++ block)
    | otherwise                             =
        throwError "Impossible situation"

moveToExpression :: MonadIO m => Int -> Maybe [Assignment] -> ExpressionT m (Maybe Expression)
moveToExpression _ Nothing      = return Nothing
moveToExpression mc (Just a)    = do
    e <- assignmentToExpression mc a
    return (Just e)

goalFor :: Player -> CompiledSpec -> Int -> Expression
goalFor Existential spec i  = (cg spec) !! i
goalFor Universal spec i    = (ug spec) !! i

leafTo :: CompiledSpec -> Int -> Int -> Player -> Int -> Int -> SolverT ([(Maybe Int, Expression)], Expression)
leafTo spec copy maxCopy player rank rankTo = do
    let CompiledSpec{..}    = spec

    if rank == rankTo
    then do
        let g   = goalFor player spec rankTo
        cachedGoal <- liftE $ getCached rank copy copy copy (exprIndex g)
        when (isNothing cachedGoal) $ throwError $ "leafTo: Goal was not created in advance: " ++ show (rank, copy)
        return ([], fromJust cachedGoal)
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
    let moveMap = if player == Existential
        then defaultUnMoves ls
        else defaultExMoves ls
    if Map.null moveMap
    then return gt
    else do
        let gt' = if gtPlayer gt == opponent player && isNothing (gtMove gt)
            then gtSetMove gt (fromJust (Map.lookup (gtRank gt) moveMap))
            else gt

        let cs = gtChildren gt'
        cs' <- mapM (fillTree player) cs

        return $ gtSetChildren gt' cs'

checkMoveFml :: CompiledSpec -> Player -> Int -> [Assignment] -> [Assignment] -> SolverT (Maybe Expression)
checkMoveFml spec player rank move1 move2 = do
    liftE $ clearTempExpressions
    liftE $ initCopyMaps 0

    let m1      = map (\a -> setAssignmentRankCopy a 1 0) move1
    let m2      = map (\a -> setAssignmentRankCopy a 1 0) move2

    m1e         <- liftE $ assignmentToExpression 0 m1
    m2e         <- liftE $ assignmentToExpression 0 m2

    step        <- liftE $ getCached 1 0 0 0 (exprIndex (t spec !! 0))

    losingStates <- if player == Universal
        then do
            ls          <- get
            let lose    = map Set.toList (Set.toList (winningMust ls))
            return (Just lose, Just lose)
        else do
            ls          <- get
            let lose1   = fmap (map Set.toList . Set.toList) (Map.lookup rank (winningMay ls))
            let lose0   = fmap (map Set.toList . Set.toList) (Map.lookup (rank-1) (winningMay ls))
            return (lose1, lose0)


    case losingStates of
        (Just lose1', Just lose0')  -> do
            let lose1   = map (map (\a -> setAssignmentRankCopy a 1 0)) lose1'
            let lose0   = map (map (\a -> setAssignmentRankCopy a 0 0)) lose0'

            lose1e      <- liftE $ mapM (assignmentToExpression 0) lose1
            lose1eD     <- liftE $ if (null lose1e) then falseExpr else disjunctTemp 0 lose1e
            lose0e      <- liftE $ mapM (assignmentToExpression 0) lose0
            lose0eD     <- liftE $ if (null lose0e) then falseExpr else disjunctTemp 0 lose0e

            notLosing1  <- liftE $ negationTemp 0 lose1eD
            notLosing0  <- liftE $ negationTemp 0 lose0eD

            e <- liftE $ conjunctTemp 0 [fromJust step, m1e, m2e, notLosing0, notLosing1]

            return $ Just e

        _ -> return Nothing
