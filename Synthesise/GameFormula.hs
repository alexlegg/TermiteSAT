{-# LANGUAGE RecordWildCards #-}
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
    let root    = gtRoot gt
    let rank    = gtRank root
    liftE $ clearTempExpressions
    initMove    <- liftE $ moveToExpression (gtMaxCopy gt) (gtMove root)
    let s'      = s : catMaybes [initMove]
    let maxCopy = gtMaxCopy gt

    block <- makeBlockingExpressions player rank maxCopy

    if null (gtChildren root)
    then do
        let transitions = sortTransitions $ getTransitions rank root (Nothing, Nothing, Nothing)
        mapM (makeTransitions spec (gtFirstPlayer gt)) transitions

        (es, fml)   <- leafToBottom spec 0 maxCopy player rank
        fml'        <- liftE $ conjunctTemp maxCopy (fml : s' ++ block)
        return ([map snd es], fml', root)

    else do
        let cs      = concatMap gtMovePairs (gtChildren root)
        let transitions = sortTransitions $ concatMap (getTransitions rank root) cs
        mapM (makeTransitions spec (gtFirstPlayer gt)) transitions

        steps       <- mapM (makeSteps rank spec player (gtFirstPlayer gt) root) cs
        moves       <- concatMapM (makeMoves rank spec player (gtFirstPlayer gt) root) cs
        step        <- liftE $ conjunctTemp maxCopy (map snd steps)

        let es = map (step :) (concatMap (map (map snd) . fst) steps)
        let n2e = (gtNodeId root, step) : concatMap (concatMap catMaybeFst . fst) steps
        let gt' = gtSetExprIds player (map (mapSnd exprIndex) n2e) root

        fml'        <- liftE $ conjunctTemp maxCopy (step : s' ++ block ++ (catMaybes moves))
        return (es, fml', gt')

makeMoves :: Int -> CompiledSpec -> Player -> Player -> GameTree -> (Move, Move, Maybe GameTree) -> SolverT [Maybe Expression]
makeMoves rank spec player first gt (m1, m2, c) = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1
    let parentCopy          = gtCopyId gt 
    let copy1               = maybe parentCopy (gtCopyId . gtParent) c
    let copy2               = maybe copy1 gtCopyId c
    let vh                  = if player == Existential then vu else vc

    next <- if isJust c 
    then do
        let cs = map gtMovePairs (gtChildren (fromJust c))
        if not (null cs)
        then concatMapM (concatMapM (makeMoves (rank-1) spec player first (fromJust c))) cs
        else return []
    else return []

    m1' <- liftE $ makeMoveExpression (gtMaxCopy gt) m1 (player == first) (vh !! i)

    m1Copy <- case m1' of
        (Just m) -> do
            mc <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex m)
            case mc of
                (Just mc)   -> return (Just mc)
                Nothing     -> do
                    let m1Map = Map.fromList [
                              ((playerToSection first, rank), copy1)
                            , ((HatVar, rank), copy1)
                            , ((StateVar, rank), parentCopy)
                            ]
                    m1c <- liftE $ setCopy m1Map m
                    return (Just m1c)
        Nothing -> return Nothing

    m2' <- liftE $ makeMoveExpression (gtMaxCopy gt) m2 (player /= first) (vh !! i)

    m2Copy <- case m2' of
        (Just m) -> do
            mc <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex m)
            case mc of
                (Just mc)   -> return (Just mc)
                Nothing     -> do
                    let m2Map = Map.fromList [
                                  ((playerToSection (opponent first), rank), copy2)
                                , ((HatVar, rank), copy2)
                                , ((StateVar, rank), parentCopy)
                                ]
                    m2c <- liftE $ setCopy m2Map m
                    return (Just m2c)
        Nothing -> return Nothing

    return $ m1Copy : m2Copy : next

makeSteps :: Int -> CompiledSpec -> Player -> Player -> GameTree -> (Move, Move, Maybe GameTree) -> SolverT ([[(Maybe Int, Expression)]], Expression)
makeSteps rank spec player first gt (m1, m2, c) = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1
    let parentCopy          = gtCopyId gt 
    let copy1               = maybe parentCopy (gtCopyId . gtParent) c
    let copy2               = maybe copy1 gtCopyId c
    let vh                  = if player == Existential then vu else vc
    let maxCopy             = gtMaxCopy gt

    (es, next) <- if isJust c
        then do
            let cs = concatMap gtMovePairs (gtChildren (fromJust c))
            if null cs
            then do
                (es, step) <- leafToBottom spec (gtCopyId (fromJust c)) maxCopy player (rank-1)
                return ([(Just (gtNodeId (fromJust c)), step) : es], step)
            else do
                steps <- mapM (makeSteps (rank-1) spec player first (fromJust c)) cs
                conj <- liftE $ conjunctTemp (gtMaxCopy gt) (map snd steps)
                return (map ((Just (gtNodeId (fromJust c)), conj) :) (concatMap fst steps), conj)
        else do
            (es, step) <- leafToBottom spec (gtCopyId gt) maxCopy player (rank-1)
            return ([es], step)

    s <- singleStep spec rank maxCopy player parentCopy copy1 copy2 next
    return (es, s)

getTransitions :: Int -> GameTree -> (Move, Move, Maybe GameTree) -> [(Int, Int, Int, Int)]
getTransitions rank gt (_, _, c) = (rank, parentCopy, copy1, copy2) : next
    where
        parentCopy  = gtCopyId gt 
        copy1       = maybe parentCopy (gtCopyId . gtParent) c
        copy2       = maybe copy1 gtCopyId c
        next        = if isJust c && rank >= 1
            then case (concatMap gtMovePairs (gtChildren (fromJust c))) of
                []  -> map (\x -> (x, copy2, copy2, copy2)) (reverse [1..(rank-1)])
                cs  -> concatMap (getTransitions (rank-1) (fromJust c)) cs
            else map (\x -> (x, copy2, copy2, copy2)) (reverse [1..(rank-1)])

makeTransitions :: CompiledSpec -> Player -> (Int, Int, Int, Int) -> SolverT ()
makeTransitions spec first (rank, parentCopy, copy1, copy2) = do
    let i                   = rank - 1
    let CompiledSpec{..}    = spec

    if rank > 0
    then do
        step <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex (t !! i))

        when (not (isJust step)) $ do
            step <- if copy1 == 0 && copy2 == 0 && parentCopy == 0
                then return (t !! i)
                else do
                    let cMap = Map.fromList [
                                  ((playerToSection first, rank), copy1)
                                , ((playerToSection (opponent first), rank), copy2)
                                , ((StateVar, rank-1), copy2)
                                , ((StateVar, rank), parentCopy)
                                ]
                    liftE $ setCopy cMap (t !! i)
            liftE $ cacheStep rank parentCopy copy1 copy2 (exprIndex (t !! i)) step
    else return ()

sortTransitions :: [(Int, Int, Int, Int)] -> [(Int, Int, Int, Int)]
sortTransitions = sortBy f
    where f (_, x1, y1, z1) (_, x2, y2, z2) = compare (maximum [x1, y1, z1]) (maximum [x2, y2, z2])

singleStep spec rank maxCopy player parentCopy copy1 copy2 next = do
    let i                   = rank - 1
    let CompiledSpec{..}    = spec

    goal <- liftE $ goalFor maxCopy player (g !! i)
    goalc <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex goal)
    goal <- case goalc of
        (Just g)    -> return g
        Nothing     -> liftE $ setCopy (Map.singleton (StateVar, (rank-1)) copy2) goal

    goal <- if player == Existential
        then liftE $ disjunctTemp maxCopy [next, goal]
        else liftE $ conjunctTemp maxCopy [next, goal]

    step <- liftE $ getCached rank parentCopy copy1 copy2 (exprIndex (t !! i))
    when (isNothing step) $ throwError $ "Transition was not created in advance: " ++ show (rank, parentCopy, copy1, copy2)
    liftE $ conjunctTemp maxCopy [fromJust step, goal]

makeBlockingExpressions :: Player -> Int -> Int -> SolverT [Expression]
makeBlockingExpressions player rank copy = do
    LearnedStates{..} <- get
    if player == Existential
        then do
            concatMapM (makeBlockEx winningUn) (concatMap (\r -> map (\c -> (r, c)) [0..copy]) [0..rank])
        else do
            concatMapM (\(r, c) -> blockExpression winningEx r c) [(r, c) | r <- [0..rank], c <- [0..copy]]

blockExpression as rank copy = do
    liftE $ forM (map (map (\a -> setAssignmentRankCopy a rank copy)) as) $ \a -> do
        cached <- getCachedMove copy (BlockedState, a)
        case cached of
            (Just b)    -> return b
            Nothing     -> do
                b <- blockAssignment copy a
                cacheMove (BlockedState, a) b
                return b

makeBlockEx blocking (rank, copy) = do
    let as = fromMaybe [] (Map.lookup rank blocking)
    blockExpression as rank copy

makeMoveExpression mc Nothing _ _       = return Nothing
makeMoveExpression mc (Just a) hat vars = do
    let mType = if hat then HatMove else RegularMove
    cached <- getCachedMove mc (mType, a)
    case cached of
        (Just m)    -> return (Just m)
        Nothing     -> do
            move <- if hat
                then assignmentToExpression mc a
                else makeHatMove mc vars a
            let mType = if hat then HatMove else RegularMove
            cacheMove (mType, a) move
            return $ Just move

moveToExpression mc Nothing    = return Nothing
moveToExpression mc (Just a)   = do
    e <- assignmentToExpression mc a
    return (Just e)

-- Ensures that a player can't force the other player into an invalid move
makeHatMove mc valid m = do
    move <- assignmentToExpression mc m
    move_hat <- setHatVar move
    valid_hat <- setHatVar valid
    imp <- implicateTemp mc valid_hat move
    conjunctTemp mc [move_hat, imp]

goalFor _ Existential g = return g
goalFor mc Universal g  = negationTemp mc g

leafToBottom :: CompiledSpec -> Int -> Int -> Player -> Int -> SolverT ([(Maybe Int, Expression)], Expression)
leafToBottom spec copy maxCopy player rank = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1

    if rank == 0
    then do
        g   <- liftE $ goalFor maxCopy player (g !! 0)
        cg  <- liftE $ setCopy (Map.singleton (StateVar, rank) copy) g
        return ([], cg)
    else do
        (es, next) <- leafToBottom spec copy maxCopy player (rank - 1)

        step <- singleStep spec rank maxCopy player copy copy copy next
        return ((Nothing, step) : es, step)

playerToSection :: Player -> Section
playerToSection Existential = ContVar
playerToSection Universal   = UContVar
