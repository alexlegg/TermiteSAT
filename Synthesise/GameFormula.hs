{-# LANGUAGE RecordWildCards, ExistentialQuantification, TypeSynonymInstances #-}
module Synthesise.GameFormula (
      makeFml
---    , getStepExpressions
    ) where

import qualified Data.Map as Map
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

makeFml :: CompiledSpec -> Player -> Expression -> GameTree -> SolverT ([[Expression]], Expression, GameTree)
makeFml spec player s ogt = do
    let gt      = normaliseCopies ogt
    let maxCopy = gtMaxCopy gt
    let root    = gtRoot gt
    let rank    = gtRank root

    liftE $ clearTempExpressions
    liftE $ initCopyMaps maxCopy

    -- Construct init expression
    initMove    <- liftE $ moveToExpression (gtMaxCopy gt) (gtMove root)
    let s'      = s : catMaybes [initMove]

    -- Make a list of transitions, moves and blocking expressions to construct
    let cs      = gtSteps root
    let trans   = map Construct $ if null cs
                    then getTransitions rank root (Nothing, Nothing, Nothing)
                    else concatMap (getTransitions rank root) cs
    let moves   = map Construct $ concatMap (getMoves rank root) cs
    block'      <- getBlockedStates player rank maxCopy
    let block   = map Construct block'

---    liftIO $ putStrLn "----------------------------------"
---    liftIO $ mapM (putStrLn . show) (sortConstructibles (trans ++ moves {- ++ block -}))
---    liftIO $ putStrLn "----------------------------------"

    -- Construct everything in order
    exprs       <- mapM (construct spec player (gtFirstPlayer gt)) (sortConstructibles (trans ++ moves {- ++ block -}))

    -- Join transitions into steps and finally fml
    (es, fml)   <- case gtStepChildren root of
        []  -> do
            (es, step)  <- leafToBottom spec 0 maxCopy player rank
            return ([(Just (gtNodeId root), step) : es], step)
        scs -> do
            steps       <- mapM (makeSteps rank spec player root) scs
            step        <- liftE $ conjunctTemp maxCopy (map snd steps)
            return (map ((Just (gtNodeId root), step) :) (concatMap fst steps), step)

    fml'        <- liftE $ conjunctTemp maxCopy (fml : s' ++ catMaybes exprs)

    -- Gametree and expression bookkeeping
    let node2expr   = concatMap catMaybeFst es
    let gt'         = gtSetExprIds player (map (mapSnd exprIndex) node2expr) root

    return (map (map snd) es, fml', gt')

class Constructible a where
    sortIndex   :: a -> Int
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
    sortIndex CMove{..}     = 0
    construct s p f         = makeMove s p

data CTransition = CTransition {
      ctRank        :: Int
    , ctParentCopy  :: Int
    , ctCopy1       :: Int
    , ctCopy2       :: Int
    } deriving (Show, Eq)

instance Constructible CTransition where
    sortIndex CTransition{..}   = maximum [ctParentCopy, ctCopy1, ctCopy2]
    construct s p f             = makeTransition s f

data CBlocked = CBlocked {
      cbRank        :: Int
    , cbCopy        :: Int
    , cbAssignment  :: [Assignment]
    } deriving (Show, Eq)

instance Constructible CBlocked where
    sortIndex CBlocked{..}  = cbCopy
    construct _ _ _         = blockExpression

data Construct = forall a . (Constructible a, Show a) => Construct a

instance Show Construct where
    show (Construct x) = show x

instance Constructible Construct where
    sortIndex (Construct x)         = sortIndex x
    construct s p f (Construct x)   = construct s p f x

getMoves :: Int -> GameTree -> (Move, Move, Maybe GameTree) -> [CMove]
getMoves rank gt (m1, m2, c) = m1' ++ m2' ++ next
    where
        m1'         = maybe [] (\m -> [CMove rank parentCopy copy1 first m]) m1
        m2'         = maybe [] (\m -> [CMove rank parentCopy copy2 (opponent first) m]) m2
        parentCopy  = gtCopyId gt 
        copy1       = maybe parentCopy (gtCopyId . gtParent) c
        copy2       = maybe copy1 gtCopyId c
        first       = gtFirstPlayer gt
        next        = if isJust c && rank >= 1
            then concatMap (getMoves (rank-1) (fromJust c)) (gtSteps (fromJust c))
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

getBlockedStates :: Player -> Int -> Int -> SolverT [CBlocked]
getBlockedStates Existential rank copy = do
    LearnedStates{..} <- get
    return $ concatMap (\r -> concatMap (blockAtRank winningUn r) [0..copy]) [0..rank]
    where
        blockAtRank block r c = map (CBlocked r c) (fromMaybe [] (Map.lookup r block))
getBlockedStates Universal rank copy = do
    LearnedStates{..} <- get
    return $ [CBlocked r c a | r <- [0..rank], c <- [0..copy], a <- winningEx]

blockExpression CBlocked{..} = do
    let as = map (\a -> setAssignmentRankCopy a cbRank cbCopy) cbAssignment
    cached <- liftE $ getCachedMove cbCopy (BlockedState, as)
    case cached of
        (Just b)    -> return (Just b)
        Nothing     -> do
            b <- liftE $ blockAssignment cbCopy as
            liftE $ cacheMove cbCopy (BlockedState, as) b
            return (Just b)

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
    else return Nothing

makeSteps :: Int -> CompiledSpec -> Player -> GameTree -> GameTree -> SolverT ([[(Maybe Int, Expression)]], Expression)
makeSteps rank spec player gt c = do
    let parentCopy          = gtCopyId gt 
    let copy1               = gtCopyId (gtParent c)
    let copy2               = gtCopyId c
    let maxCopy             = gtMaxCopy gt

    (es, next) <- case gtStepChildren c of
        [] -> do
            (es, step) <- leafToBottom spec copy2 maxCopy player (rank-1)
            return ([(Just (gtNodeId c), step) : es], step)
        cs -> do
            steps <- mapM (makeSteps (rank-1) spec player c) cs
            conj <- liftE $ conjunctTemp maxCopy (map snd steps)
            return (map ((Just (gtNodeId c), conj) :) (concatMap fst steps), conj)

    s <- singleStep spec rank maxCopy player parentCopy copy1 copy2 next
    return (es, s)

makeMove :: CompiledSpec -> Player -> CMove -> SolverT (Maybe Expression)
makeMove spec player CMove{..} = do
    let CompiledSpec{..}    = spec
    let vh                  = if cmPlayer == Universal then vu else vc
    let i                   = cmRank - 1
    let isHatMove           = player == cmPlayer

    move <- if isHatMove
        then liftE $ assignmentToExpression 0 cmAssignment
        else liftE $ makeHatMove (vh !! i) cmAssignment

    let cMap = Map.fromList [
              ((playerToSection cmPlayer, cmRank), cmCopy)
            , ((HatVar, cmRank), cmCopy)
            , ((StateVar, cmRank), cmParentCopy)
            ]

    mc <- liftE $ setCopy cMap move
    return (Just mc)

makeHatMove valid m = do
    move        <- assignmentToExpression 0 m
    move_hat    <- setHatVar 0 move
    valid_hat   <- setHatVar 0 valid
    imp         <- implicate valid_hat move
    conjunct [move_hat, imp]

singleStep spec rank maxCopy player parentCopy copy1 copy2 next = do
    let i                   = rank - 1
    let CompiledSpec{..}    = spec

    let goal = goalFor player spec i

---    goalc <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex goal)
---    goal <- case goalc of
---        (Just g)    -> return g
---        Nothing     -> liftE $ setCopy (Map.singleton (StateVar, (rank-1)) copy2) goal

    goal <- liftE $ setCopy (Map.singleton (StateVar, (rank-1)) copy2) goal

    goal <- if player == Existential
        then liftE $ disjunctTemp maxCopy [next, goal]
        else liftE $ conjunctTemp maxCopy [next, goal]

    step <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex (t !! i))
    when (isNothing step) $ throwError $ "Transition was not created in advance: " ++ show (rank, parentCopy, copy1, copy2)

    liftE $ conjunctTemp maxCopy [fromJust step, goal]

---makeBlockingExpressions :: Player -> Int -> Int -> SolverT [Expression]
---makeBlockingExpressions player rank copy = do
---    LearnedStates{..} <- get
---    if player == Existential
---        then do
---            concatMapM (makeBlockEx winningUn) [(r, c) | r <- [0..rank], c <- [0..copy]]
---        else do
---            concatMapM (\(r, c) -> blockExpression winningEx r c) [(r, c) | r <- [0..rank], c <- [0..copy]]

---makeBlockEx blocking (rank, copy) = do
---    let as = fromMaybe [] (Map.lookup rank blocking)
---    blockExpression as rank copy

moveToExpression mc Nothing    = return Nothing
moveToExpression mc (Just a)   = do
    e <- assignmentToExpression mc a
    return (Just e)

goalFor Existential spec i  = (cg spec) !! i
goalFor Universal spec i    = (ug spec) !! i

leafToBottom :: CompiledSpec -> Int -> Int -> Player -> Int -> SolverT ([(Maybe Int, Expression)], Expression)
leafToBottom spec copy maxCopy player rank = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1

    if rank == 0
    then do
        let g = goalFor player spec 0
        cg  <- liftE $ setCopy (Map.singleton (StateVar, rank) copy) g
        return ([], cg)
    else do
        (es, next) <- leafToBottom spec copy maxCopy player (rank - 1)

        step <- singleStep spec rank maxCopy player copy copy copy next
        return ((Nothing, step) : es, step)

playerToSection :: Player -> Section
playerToSection Existential = ContVar
playerToSection Universal   = UContVar
