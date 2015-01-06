{-# LANGUAGE RecordWildCards #-}
module Synthesise.GameFormula (
      makeFml
    , singleStep
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
        fml         <- leafToBottom spec 0 player rank
        fml'        <- liftE $ conjunct [fml, s']

        return fml'
    else do
        let cs      = map gtMovePairs (gtChildren root)
        steps       <- concatMapM (mapM (makeStep rank spec player (gtFirstPlayer gt) root)) cs
        fml'        <- liftE $ conjunct (s' : steps)
        return fml'

makeStep rank spec player first gt (m1, m2, c) = do
    let CompiledSpec{..} = spec
    let i = rank - 1

    next <- if isJust c
        then do
            let cs = map gtMovePairs (gtChildren (fromJust c))
            if null cs
            then do
                leafToBottom spec (gtCopyId (fromJust c)) player (rank-1)
            else do
                steps <- concatMapM (mapM (makeStep (rank-1) spec player first (fromJust c))) cs
                liftE $ conjunct steps
        else do
            leafToBottom spec (gtCopyId gt) player (rank-1)

    singleStep rank spec player first gt next m1 m2 c

singleStep rank spec player first parentGT next m1 m2 c = do
    let CompiledSpec{..}    = spec
    let i                   = rank - 1
    let vh                  = if player == Existential then vu else vc
    let parentCopy          = gtCopyId parentGT
    let copy1               = maybe parentCopy (gtCopyId . gtParent) c
    let copy2               = maybe copy1 gtCopyId c

    m1' <- if player == first
        then liftE $ moveToExpression m1
        else liftE $ makeHatMove (vh !! i) m1

    m1Copy <- if isJust m1'
        then do
            let m1Map = Map.fromList [
                              ((playerToSection first, rank), copy1)
                            , ((HatVar, rank), copy1)
                            , ((StateVar, rank), parentCopy)
                            ]
            m1c <- liftE $ setCopy m1Map (fromJust m1')
            return (Just m1c)
        else return Nothing

    m2' <- if player == first
        then liftE $ makeHatMove (vh !! i) m2
        else liftE $ moveToExpression m2

    m2Copy <- if isJust m2'
        then do
            let m2Map = Map.fromList [
                          ((playerToSection (opponent first), rank), copy2)
                        , ((HatVar, rank), copy2)
                        , ((StateVar, rank), parentCopy)
                        ]
            m2c <- liftE $ setCopy m2Map (fromJust m2')
            return (Just m2c)
        else return Nothing

    block <- blockLosingStates rank player
    block <- if isJust block
        then (liftM Just) $ liftE $ setCopy (Map.singleton (StateVar, rank) parentCopy) (fromJust block)
        else return Nothing

    goal <- liftE $ goalFor player (g !! i)
    goal <- liftE $ setCopy (Map.singleton (StateVar, (rank-1)) copy2) goal
    goal <- if player == Existential
        then liftE $ disjunct [next, goal]
        else liftE $ conjunct [next, goal]

    step <- liftE $ getCached (rank, parentCopy, copy1, copy2)
    step <- if isJust step then (return (fromJust step)) else do
        step    <- liftE $ conjunct [t !! i, vc !! i, vu !! i]
        let cMap = Map.fromList [
                      ((playerToSection first, rank), copy1)
                    , ((playerToSection (opponent first), rank), copy2)
                    , ((StateVar, rank-1), copy2)
                    , ((StateVar, rank), parentCopy)
                    ]
        step    <- liftE $ setCopy cMap step

        liftE $ cacheStep (rank, parentCopy, copy1, copy2) step
        return step

    let moves = catMaybes [m1Copy, m2Copy, block]
    liftE $ conjunct (step : goal : moves)

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

leafToBottom :: CompiledSpec -> Int -> Player -> Int -> SolverT Expression
leafToBottom spec copy player rank = do
    let CompiledSpec{..} = spec
    let i = rank - 1

    when (rank < 0) $ throwError "leafToBottom called on a tree that's too long"

    if rank == 0
    then do
        g <- liftE $ goalFor player (g !! 0)
        liftE $ setCopy (Map.singleton (StateVar, rank) copy) g
    else do
        goal <- if rank == 1
            then liftE $ goalFor player (g !! i)
            else do
                next <- leafToBottom spec copy player (rank-1)
                g' <- liftE $ goalFor player (g !! i)
                if player == Existential
                    then liftE $ disjunct [next, g']
                    else liftE $ conjunct [next, g']

        block <- blockLosingStates rank player
        fml <- if isJust block
            then liftE $ conjunct [t !! i, vu !! i, vc !! i, goal, fromJust block]
            else liftE $ conjunct [t !! i, vu !! i, vc !! i, goal]

        let cMap = Map.fromList [
                      ((UContVar, rank), copy)
                    , ((ContVar, rank), copy)
                    , ((StateVar, rank), copy)
                    , ((StateVar, rank-1), copy)
                    ]
        liftE $ setCopy cMap fml

playerToSection :: Player -> Section
playerToSection Existential = ContVar
playerToSection Universal   = UContVar
