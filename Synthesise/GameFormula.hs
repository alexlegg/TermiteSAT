{-# LANGUAGE RecordWildCards, ExistentialQuantification, ViewPatterns #-}
module Synthesise.GameFormula (
      makeFml
    , makeSplitFmls
    , makeInitCheckFml
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

makeFml :: CompiledSpec -> Player -> Expression -> GameTree -> Bool -> SolverT ([[Expression]], Expression, GameTree)
makeFml spec player s ogt useBlocking = do
    let gt      = normaliseCopies ogt
    let maxCopy = gtMaxCopy gt
    let root    = gtRoot gt
    let rank    = gtRank root

    liftE $ clearTempExpressions
    liftE $ initCopyMaps maxCopy

    -- Make a list of transitions, moves and blocking expressions to construct
    let cs      = gtSteps root
    let trans   = map Construct $ if null cs
                    then getTransitions rank root (Nothing, Nothing, Nothing)
                    else concatMap (getTransitions rank root) cs
    let goals   = map Construct $ getGoals rank maxCopy player
    let moves   = map Construct $ concatMap (getMoves rank player root) cs
    block       <- if useBlocking
                    then (liftM (map Construct)) $ getBlockedStates player rank maxCopy
                    else return []
---                    
---    block'      <- getBlockedStates player rank maxCopy
---    let block   = map Construct block'

    -- Construct everything in order
    exprs       <- mapM (construct spec player (gtFirstPlayer gt)) (sortConstructibles (trans ++ moves ++ goals ++ block))

    -- Construct init expression
    initMove    <- liftE $ moveToExpression (gtMaxCopy gt) (gtMove root)
    let s'      = s : catMaybes [initMove]

    -- Join transitions into steps and finally fml
    (es, fml)   <- case gtStepChildren root of
        []  -> do
            (es, step)  <- leafTo spec 0 maxCopy player rank 0
            return ([(Just (gtNodeId root), step) : es], step)
        scs -> do
            steps       <- mapM (makeSteps maxCopy rank spec player Nothing root) scs
            step        <- liftE $ conjunctTemp maxCopy (map snd steps)
            return (map ((Just (gtNodeId root), step) :) (concatMap fst steps), step)

    fml'        <- liftE $ conjunctTemp maxCopy (fml : s' ++ catMaybes exprs)

    -- Gametree and expression bookkeeping
    let node2expr   = concatMap catMaybeFst es
    let gt'         = gtSetExprIds player (map (mapSnd exprIndex) node2expr) root

    return (map (map snd) es, fml', gt')

makeSplitFmls :: CompiledSpec -> Player -> Expression -> GameTree -> SolverT (Maybe (GameTree, GameTree, Expression, Expression))
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
    let nCopy   = gtCopyId t2

    liftE $ clearTempExpressions
    liftE $ initCopyMaps maxCopy

    constA <- liftM (zip (repeat True)) $ getConstructsFor maxCopy t1 player (gtBaseRank t2)
    constB <- liftM (zip (repeat False)) $ getConstructsFor maxCopy t2 player 0
    let sorted = sortBy (\x y -> compare (sortIndex (snd x)) (sortIndex (snd y))) (constA ++ constB)

    -- Construct everything in order
    exprs       <- mapM (mapSndM (construct spec player (gtFirstPlayer gt))) sorted
    let exprsA  = catMaybes $ map snd (filter fst exprs)
    let exprsB  = catMaybes $ map snd (filter (not . fst) exprs)
    
    -- Construct init expression
    initMove    <- liftE $ moveToExpression maxCopy (gtMove root)
    let s'      = s : catMaybes [initMove]

    -- Join transitions into steps and finally fml
    fmlA' <- case gtStepChildren (gtRoot t1) of
        []  -> do
            liftE $ trueExpr
        scs -> do
            steps <- mapM (makeSteps maxCopy (gtRank (gtRoot t1)) spec player (Just (nRank, nCopy)) (gtRoot t1)) scs
            liftE $ conjunctTemp maxCopy (map snd steps)

    fmlA        <- liftE $ conjunctTemp maxCopy (fmlA' : s' ++ exprsA)

    fmlB' <- case gtStepChildren (gtRoot t2) of
        []  -> do
            liftE $ trueExpr
        scs -> do
            steps <- mapM (makeSteps maxCopy (gtRank (gtRoot t2)) spec player Nothing (gtRoot t2)) scs
            liftE $ conjunctTemp maxCopy (map snd steps)

    fmlB        <- liftE $ conjunctTemp maxCopy (fmlB' : exprsB)

    return (Just (t1, t2, fmlA, fmlB))

makeInitCheckFml :: Int -> Expression -> [[Assignment]] -> Expression -> SolverT Expression
makeInitCheckFml rank init must goal = do
    liftE $ clearTempExpressions
    liftE $ initCopyMaps 0

    let must'   = map (map (\a -> setAssignmentRankCopy a rank 0)) must
    g'          <- liftE $ setRank rank goal
    ms          <- liftE $ mapM (assignmentToExpression 0) must'
    d           <- liftE $ disjunctC 0 (g' : ms)
    liftE $ conjunctC 0 [d, init]

getConstructsFor :: Int -> GameTree -> Player -> Int -> SolverT [Construct]
getConstructsFor maxCopy gt player toRank = do
    let root    = gtRoot gt
    let rank    = gtRank root
    let cs      = gtSteps root
    let trans   = map Construct $ if null cs
                    then getTransitions rank root (Nothing, Nothing, Nothing)
                    else concatMap (getTransitions rank root) cs
    let goals   = map Construct $ getGoals rank maxCopy player
    let moves   = map Construct $ concatMap (getMoves rank player root) cs
    block'      <- getBlockedStates player rank maxCopy
    let block   = map Construct $ filter (\b -> cbRank b > toRank && cbRank b <= gtBaseRank gt) block'
    return $ trans ++ goals ++ moves ++ block

class Constructible a where
    sortIndex   :: a -> Int
    cRank       :: a -> Int
    construct   :: CompiledSpec -> Player -> Player -> a -> SolverT (Maybe Expression)

sortConstructibles :: Constructible a => [a] -> [a]
sortConstructibles = sortBy (\x y -> compare (sortIndex x) (sortIndex y))

data CMove = CMove {
      cmRank         :: Int
    , cmParentCopy   :: Int
    , cmCopy         :: Int
    , cmPlayer       :: Player
    , cmAssignment   :: [Assignment]
    } deriving (Show, Eq)

instance Constructible CMove where
    sortIndex CMove{..}     = cmCopy
    cRank                   = cmRank
    construct s p f         = makeMove s p

data CTransition = CTransition {
      ctRank        :: Int
    , ctParentCopy  :: Int
    , ctCopy1       :: Int
    , ctCopy2       :: Int
    } deriving (Show, Eq)

instance Constructible CTransition where
    sortIndex CTransition{..}   = maximum [ctParentCopy, ctCopy1, ctCopy2]
    cRank                       = ctRank
    construct s p f             = makeTransition s f

data CBlocked = CBlocked {
      cbRank        :: Int
    , cbCopy        :: Int
    , cbAssignment  :: [Assignment]
    } deriving (Show, Eq)

instance Constructible CBlocked where
    sortIndex CBlocked{..}  = cbCopy
    cRank                   = cbRank
    construct _ _ _         = blockExpression

data CGoal = CGoal {
      cgRank        :: Int
    , cgCopy        :: Int
    , cgPlayer      :: Player
    } deriving (Show, Eq)

instance Constructible CGoal where
    sortIndex CGoal{..} = cgCopy
    cRank               = cgRank
    construct s p f     = makeGoal s p

data Construct = forall a . (Constructible a, Show a) => Construct a

instance Show Construct where
    show (Construct x) = show x

instance Constructible Construct where
    sortIndex (Construct x)         = sortIndex x
    construct s p f (Construct x)   = construct s p f x
    cRank (Construct x)             = cRank x

getMoves :: Int -> Player -> GameTree -> (Move, Move, Maybe GameTree) -> [CMove]
getMoves rank player gt (m1, m2, c) = m1' ++ m2' ++ next --m ++ next
    where
        m           = if player == first then m2' else m1'
        m1'         = maybe [] (\m -> [CMove rank parentCopy copy1 first m]) m1
        m2'         = maybe [] (\m -> [CMove rank parentCopy copy2 (opponent first) m]) m2
        parentCopy  = gtCopyId gt 
        copy1       = maybe parentCopy (gtCopyId . gtParent) c
        copy2       = maybe copy1 gtCopyId c
        first       = gtFirstPlayer gt
        next        = if isJust c && rank >= 1
            then concatMap (getMoves (rank-1) player (fromJust c)) (gtSteps (fromJust c))
            else []


getTransitions :: Int -> GameTree -> (Move, Move, Maybe GameTree) -> [CTransition]
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

getGoals :: Int -> Int -> Player -> [CGoal]
getGoals rank mc p = map (\(r, c) -> CGoal r c p) [(r, c) | r <- [0..rank-1], c <- [0..mc]]

makeGoal :: CompiledSpec -> Player -> CGoal -> SolverT (Maybe Expression)
makeGoal spec player CGoal{..} = do
    let g   = goalFor player spec cgRank
    cached  <- liftE $ getCached cgRank cgCopy cgCopy cgCopy (exprIndex g)
    when (isNothing cached) $ do
        cg      <- liftE $ setCopy (Map.singleton (StateVar, cgRank) cgCopy) g
        liftE $ cacheStep cgRank cgCopy cgCopy cgCopy (exprIndex g) cg
    return Nothing

getBlockedStates :: Player -> Int -> Int -> SolverT [CBlocked]
getBlockedStates Existential rank copy = do
    LearnedStates{..} <- get
    let blockingStates = case learningType of
                BoundedLearning     -> winningUn
                UnboundedLearning   -> winningMay
    return $ concatMap (\r -> concatMap (blockAtRank blockingStates r) [0..copy]) [1..rank]
    where
        blockAtRank block r c = concatMap (blockAllRanks r c) (maybe [] Set.toList (Map.lookup r block))
        blockAllRanks r c as  = map (\x -> CBlocked x c as) [1..r]
getBlockedStates Universal rank copy = do
    LearnedStates{..} <- get
    let blockingStates = case learningType of
                BoundedLearning     -> winningEx
                UnboundedLearning   -> winningMust
    return [CBlocked r c a | r <- [0..rank], c <- [0..copy], a <- blockingStates]

blockExpression CBlocked{..} = do
    let as = map (\a -> setAssignmentRankCopy a cbRank cbCopy) cbAssignment
    b <- liftE $ blockAssignment cbCopy as
    return (Just b)
---    cached <- liftE $ getCachedMove cbCopy (BlockedState, as)
---    case cached of
---        (Just b)    -> return (Just b)
---        Nothing     -> do
---            b <- liftE $ blockAssignment cbCopy as
---            be <- liftE $ printExpression b
---            liftIO $ putStrLn be
---            liftE $ cacheMove cbCopy (BlockedState, as) b
---            return (Just b)

makeTransition :: CompiledSpec -> Player -> CTransition -> SolverT (Maybe Expression)
makeTransition spec first CTransition{..} = do
    let i                   = ctRank - 1
    let CompiledSpec{..}    = spec

    if ctRank > 0
    then do
        step <- liftE $ getCached ctRank ctParentCopy ctCopy1 ctCopy2 (exprIndex (t !! i))

        when (not (isJust step)) $ do
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

makeSteps :: Int -> Int -> CompiledSpec -> Player -> Maybe (Int, Int) -> GameTree -> GameTree -> SolverT ([[(Maybe Int, Expression)]], Expression)
makeSteps maxCopy rank spec player extend gt c = do
    let parentCopy          = gtCopyId gt 
    let copy1               = gtCopyId (gtParent c)
    let copy2               = gtCopyId c

    (es, next) <- case gtStepChildren c of
        [] -> do
            if extend == Just (rank-1, copy2)
            then return ([], Nothing)
            else do
                (es, step) <- leafTo spec copy2 maxCopy player (rank-1) 0
                return ([(Just (gtNodeId c), step) : es], Just step)
        cs -> do
            steps <- mapM (makeSteps maxCopy (rank-1) spec player extend c) cs
            conj <- liftE $ conjunctTemp maxCopy (map snd steps)
            return (map ((Just (gtNodeId c), conj) :) (concatMap fst steps), Just conj)

    s <- singleStep spec rank maxCopy player parentCopy copy1 copy2 next
    return (es, s)

makeMove :: CompiledSpec -> Player -> CMove -> SolverT (Maybe Expression)
makeMove spec player CMove{..} = do
    let CompiledSpec{..}    = spec
    let vh                  = if cmPlayer == Universal then vu else vc
    let i                   = cmRank - 1
    let isHatMove           = player /= cmPlayer

    move <- if isHatMove
        then liftE $ makeHatMove cmCopy (vh !! i) cmAssignment
        else liftE $ assignmentToExpression cmCopy cmAssignment

    let cMap = Map.fromList [
              ((playerToSection cmPlayer, cmRank), cmCopy)
            , ((HatVar, cmRank), cmCopy)
            , ((StateVar, cmRank), cmParentCopy)
            ]

    mc <- liftE $ setCopy cMap move
    return (Just mc)

makeHatMove c valid m = do
    move        <- assignmentToExpression c m
    move_hat    <- setHatVar c move
    valid_hat   <- setHatVar c valid
    imp         <- implicateC c valid_hat move
    conjunctC c [move_hat, imp]

singleStep spec rank maxCopy player parentCopy copy1 copy2 next = do
    let i                   = rank - 1
    let CompiledSpec{..}    = spec

    step <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex (t !! i))
    when (isNothing step) $ throwError $ "Transition was not created in advance: " ++ show (rank, parentCopy, copy1, copy2)

    case next of
        Nothing -> return $ fromJust step
        Just n  -> do
            let goal    = goalFor player spec i
            cg          <- liftE $ getCached i copy2 copy2 copy2 (exprIndex goal)
            when (isNothing cg) $ throwError $ "Goal was not created in advance: " ++ show (i, copy2)

            goal <- if player == Existential
                then liftE $ disjunctTemp maxCopy [n, fromJust cg]
                else liftE $ conjunctTemp maxCopy [n, fromJust cg]

            liftE $ conjunctTemp maxCopy [fromJust step, goal]

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

        step <- singleStep spec rank maxCopy player copy copy copy (Just next)
        return ((Nothing, step) : es, step)

leafToNoGoal :: CompiledSpec -> Int -> Int -> Player -> Int -> Int -> SolverT ([(Maybe Int, Expression)], Maybe Expression)
leafToNoGoal spec copy maxCopy player rank rankTo = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1

    if rank == rankTo
    then do
        g <- liftE $ trueExpr
        return ([], Nothing)
    else do
        (es, next) <- leafToNoGoal spec copy maxCopy player (rank - 1) rankTo

        step <- singleStep spec rank maxCopy player copy copy copy next
        return ((Nothing, step) : es, Just step)

playerToSection :: Player -> Section
playerToSection Existential = ContVar
playerToSection Universal   = UContVar
