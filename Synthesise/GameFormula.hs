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
    initMove    <- liftE $ moveToExpression (gtMove root)
    let s'      = s : catMaybes [initMove]
    let maxCopy = gtMaxCopy gt

    block <- makeBlockingExpressions player rank maxCopy

    if null (gtChildren root)
    then do
        (es, fml)   <- leafToBottom spec 0 (gtFirstPlayer gt) player rank
        fml'        <- liftE $ conjunctQuick (fml : s' ++ block)

        return ([map snd es], fml', root)
    else do
        let cs      = concatMap gtMovePairs (gtChildren root)
        steps       <- mapM (makeSteps rank spec player (gtFirstPlayer gt) root) cs
        moves       <- concatMapM (makeMoves rank spec player (gtFirstPlayer gt) root) cs

        step        <- liftE $ conjunctQuick (map snd steps)

        let es = map (step :) (concatMap (map (map snd) . fst) steps)
        let n2e = (gtNodeId root, step) : concatMap (concatMap catMaybeFst . fst) steps
        let gt' = gtSetExprIds player (map (mapSnd exprIndex) n2e) root
---        liftIO $ putStrLn (printTree spec gt')

        fml'        <- liftE $ conjunctQuick (step : s' ++ block ++ (catMaybes moves))
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

    m1' <- liftE $ makeMoveExpression m1 (player == first) (vh !! i)

    m1Copy <- case m1' of
        (Just m) -> do
            mc <- liftE $ getCached (rank, parentCopy, copy1, copy2, exprIndex m)
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

    m2' <- liftE $ makeMoveExpression m2 (player /= first) (vh !! i)

    m2Copy <- case m2' of
        (Just m) -> do
            mc <- liftE $ getCached (rank, parentCopy, copy1, copy2, exprIndex m)
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

    (es, next) <- if isJust c
        then do
            let cs = concatMap gtMovePairs (gtChildren (fromJust c))
            if null cs
            then do
                (es, step) <- leafToBottom spec (gtCopyId (fromJust c)) first player (rank-1)
                return ([(Just (gtNodeId (fromJust c)), step) : es], step)
            else do
                steps <- mapM (makeSteps (rank-1) spec player first (fromJust c)) cs
                conj <- liftE $ conjunct (map snd steps)
                return (map ((Just (gtNodeId (fromJust c)), conj) :) (concatMap fst steps), conj)
        else do
            (es, step) <- leafToBottom spec (gtCopyId gt) first player (rank-1)
            return ([es], step)

    s <- singleStep spec rank first player parentCopy copy1 copy2 next
    return (es, s)

singleStep spec rank first player parentCopy copy1 copy2 next = do
    let i                   = rank - 1
    let CompiledSpec{..}    = spec

    goal <- liftE $ goalFor player (g !! i)
    goalc <- liftE $ getCached (rank, parentCopy, copy1, copy2, exprIndex goal)
    goal <- case goalc of
        (Just g)    -> return g
        Nothing     -> liftE $ setCopy (Map.singleton (StateVar, (rank-1)) copy2) goal

    goal <- if player == Existential
        then liftE $ disjunct [next, goal]
        else liftE $ conjunct [next, goal]

    step <- liftE $ getCached (rank, parentCopy, copy1, copy2, exprIndex (t !! i))

    step <- if isJust step
        then return (fromJust step)
        else do
            step <- if copy1 == 0 && copy2 == 0 && parentCopy == 0
                then return (t !! i)
                else do
                    let cMap = Map.fromList [
                                  ((playerToSection first, rank), copy1)
                                , ((playerToSection (opponent first), rank), copy2)
                                , ((StateVar, rank-1), copy2)
                                , ((StateVar, rank), parentCopy)
                                ]
                    liftE $ setCopyStep cMap (t !! i)
            liftE $ cacheStep (rank, parentCopy, copy1, copy2, exprIndex (t !! i)) step
            return step

    liftE $ conjunct [step, goal]

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
        cached <- getCachedMove (BlockedState, a)
        case cached of
            (Just b)    -> return b
            Nothing     -> do
                b <- blockAssignment a
                cacheMove (BlockedState, a) b
                return b

makeBlockEx blocking (rank, copy) = do
    let as = fromMaybe [] (Map.lookup rank blocking)
    blockExpression as rank copy

makeMoveExpression Nothing _ _          = return Nothing
makeMoveExpression (Just a) hat vars    = do
    let mType = if hat then HatMove else RegularMove
    cached <- getCachedMove (mType, a)
    case cached of
        (Just m)    -> return (Just m)
        Nothing     -> do
            move <- if hat
                then assignmentToExpression a
                else makeHatMove vars a
            let mType = if hat then HatMove else RegularMove
            cacheMove (mType, a) move
            return $ Just move

moveToExpression Nothing    = return Nothing
moveToExpression (Just a)   = do
    e <- assignmentToExpression a
    return (Just e)

-- Ensures that a player can't force the other player into an invalid move
makeHatMove valid m = do
    move <- assignmentToExpression m
    move_hat <- setHatVar move
    valid_hat <- setHatVar valid
    imp <- implicate valid_hat move
    conjunct [move_hat, imp]

goalFor Existential g   = return g
goalFor Universal g     = negation g

leafToBottom :: CompiledSpec -> Int -> Player -> Player -> Int -> SolverT ([(Maybe Int, Expression)], Expression)
leafToBottom spec copy first player rank = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1

    if rank == 0
    then do
        g   <- liftE $ goalFor player (g !! 0)
        cg  <- liftE $ setCopy (Map.singleton (StateVar, rank) copy) g
        return ([], cg)
    else do
        (es, next) <- leafToBottom spec copy first player (rank - 1)

        step <- singleStep spec rank first player copy copy copy next
        return ((Nothing, step) : es, step)

playerToSection :: Player -> Section
playerToSection Existential = ContVar
playerToSection Universal   = UContVar

---getStepExpressions :: CompiledSpec -> GameTree -> SolverT [[Expression]]
---getStepExpressions spec gt = do
---    let root    = gtRoot gt
---    let rank    = gtRank root

---    if null (gtChildren root)
---    then return []
---    else do
---        let cs      = concatMap (map thd3 . gtMovePairs) (gtChildren root)
---        concatMapM (getStepExpr rank spec root) cs

---getStepExpr :: Int -> CompiledSpec -> GameTree -> Maybe GameTree -> SolverT [[Expression]]
---getStepExpr rank spec parent child = do
---    let CompiledSpec{..}    = spec
---    let i                   = rank - 1
---    let parentCopy          = gtCopyId parent
---    let copy1               = maybe parentCopy (gtCopyId . gtParent) child
---    let copy2               = maybe copy1 gtCopyId child

---    step <- liftE $ getCached (rank, parentCopy, copy1, copy2, exprIndex (t !! i))

---    if isJust child
---    then do
---        let cs = concatMap (map thd3 . gtMovePairs) (gtChildren (fromJust child))
---        if null cs
---        then do
---            steps <- liftE $ mapM (\r -> getCached (r, copy2, copy2, copy2, exprIndex (t !! (r-1)))) (reverse [1..rank-1])
---            return [fromJust step : map fromJust steps]
---        else do
---            steps   <- concatMapM (getStepExpr (rank-1) spec (fromJust child)) cs
---            return (map (fromJust step :) steps)
---    else do
---        steps <- liftE $ mapM (\r -> getCached (r, copy2, copy2, copy2, exprIndex (t !! (r-1)))) (reverse [1..rank-1])
---        return [fromJust step : map fromJust steps]
