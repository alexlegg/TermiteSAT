{-# LANGUAGE RecordWildCards #-}
module Synthesise.GameFormula (
      makeFml
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

makeFml spec player s gt = do
    let root    = gtRoot gt
    let rank    = gtRank root
    initMove    <- liftE $ moveToExpression (gtMove root)
    s'          <- liftE $ maybeM s (\i -> conjunct [s, i]) initMove

    if null (gtChildren root)
    then do
        fml         <- leafToBottom spec 0 (gtFirstPlayer gt) player rank
        fml'        <- liftE $ conjunct [fml, s']

        return fml'
    else do
        let cs      = map gtMovePairs (gtChildren root)
        steps       <- concatMapM (mapM (makeStep rank spec player (gtFirstPlayer gt) root)) cs
        fml'        <- liftE $ conjunct (s' : steps)
        return fml'

makeStep rank spec player first gt (m1, m2, c) = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1
    let parentCopy          = gtCopyId gt 
    let copy1               = maybe parentCopy (gtCopyId . gtParent) c
    let copy2               = maybe copy1 gtCopyId c
    let vh                  = if player == Existential then vu else vc

    next <- if isJust c
        then do
            let cs = map gtMovePairs (gtChildren (fromJust c))
            if null cs
            then do
                leafToBottom spec (gtCopyId (fromJust c)) first player (rank-1)
            else do
                steps <- concatMapM (mapM (makeStep (rank-1) spec player first (fromJust c))) cs
                liftE $ conjunct steps
        else do
            leafToBottom spec (gtCopyId gt) first player (rank-1)

    m1' <- if player == first
        then liftE $ moveToExpression m1
        else liftE $ makeHatMove (vh !! i) m1

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

    m2' <- if player == first
        then liftE $ makeHatMove (vh !! i) m2
        else liftE $ moveToExpression m2

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

    step <- singleStep spec rank first player parentCopy copy1 copy2 next

    let moves = catMaybes [m1Copy, m2Copy]
    liftE $ conjunct (step : moves)

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

    block <- blockLosingStates rank player
    block <- if isJust block
        then do
            blockc <- liftE $ getCached (rank, parentCopy, copy1, copy2, exprIndex (fromJust block))
            case blockc of
                (Just b)    -> return (Just b)
                Nothing     -> (liftM Just) $ liftE $ setCopy (Map.singleton (StateVar, rank) parentCopy) (fromJust block)
        else return Nothing

    stepc <- liftE $ conjunct [t !! i, vc !! i, vu !! i]
    step <- liftE $ getCached (rank, parentCopy, copy1, copy2, exprIndex stepc)

    if isJust step
    then do
        liftE $ conjunct (fromJust step : goal : catMaybes [block])
    else do
        stepc   <- liftE $ conjunct [t !! i, vc !! i, vu !! i]
        let cMap = Map.fromList [
                      ((playerToSection first, rank), copy1)
                    , ((playerToSection (opponent first), rank), copy2)
                    , ((StateVar, rank-1), copy2)
                    , ((StateVar, rank), parentCopy)
                    ]
        step    <- liftE $ setCopyStep cMap stepc
        liftE $ cacheStep (rank, parentCopy, copy1, copy2, exprIndex stepc) step
        liftE $ conjunct (step : goal : catMaybes [block])

blockLosingStates rank player = do
    LearnedStates{..} <- get
    let block = if player == Existential
        then fromMaybe [] (Map.lookup (rank - 1) winningUn)
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

leafToBottom :: CompiledSpec -> Int -> Player -> Player -> Int -> SolverT Expression
leafToBottom spec copy first player rank = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1

    when (rank < 0) $ throwError "leafToBottom called on a tree that's too long"

    if rank == 0
    then do
        g <- liftE $ goalFor player (g !! 0)
        liftE $ setCopy (Map.singleton (StateVar, rank) copy) g
    else do
        next <- leafToBottom spec copy first player (rank - 1)

        singleStep spec rank first player copy copy copy next

playerToSection :: Player -> Section
playerToSection Existential = ContVar
playerToSection Universal   = UContVar
