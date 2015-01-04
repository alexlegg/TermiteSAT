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

    liftIO $ putStrLn ""
    liftIO $ putStrLn ""
    liftIO $ putStrLn "makeFml"

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

    g' <- liftE $ goalFor player (g !! i)
    goal <- if player == Existential
        then liftE $ disjunct [next, g']
        else liftE $ conjunct [next, g']


    singleStep rank spec player first gt goal m1 m2 c

singleStep rank spec player first parentGT goal m1 m2 c = do
    let CompiledSpec{..} = spec
    let i   = rank - 1
    let vh  = if player == Existential then vu else vc
    let copy1 = maybe (gtCopyId parentGT) (gtCopyId . gtParent) c
    let copy2 = maybe copy1 gtCopyId c

    liftIO $ putStrLn (show (copy1, printMove spec m1, copy2, printMove spec m2))

    m1' <- if player == first
        then liftE $ moveToExpression m1
        else liftE $ makeHatMove (vh !! i) m1

    m1Copy <- if isJust m1'
        then (liftM Just) $ liftE $ setCopy (playerToSection first) rank copy1 (fromJust m1')
        else return Nothing

    m2' <- if player == first
        then liftE $ makeHatMove (vh !! i) m2
        else liftE $ moveToExpression m2

    m2Copy <- if isJust m2'
        then (liftM Just) $ liftE $ setCopy (playerToSection (opponent first)) rank copy2 (fromJust m2')
        else return Nothing

    block <- return Nothing --blockLosingStates rank player

    tCopy'' <- liftE $ setCopy (playerToSection first) rank copy1 (t !! i)
    tCopy'  <- liftE $ setCopy (playerToSection (opponent first)) rank copy2 (t !! i)
    tCopy   <- liftE $ setCopy StateVar (rank-1) copy2 (t !! i)
    gCopy   <- liftE $ setCopy StateVar (rank-1) copy2 goal
    vcCopy  <- liftE $ setCopy ContVar rank copy1 (vc !! i)
    vuCopy  <- liftE $ setCopy UContVar rank copy2 (vu !! i)

    let moves = catMaybes [m1Copy, m2Copy, block]
    liftE $ conjunct ([tCopy, vuCopy, vcCopy, gCopy] ++ moves)

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
    then liftE $ goalFor player (g !! 0)
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

        fml'  <- liftE $ setCopy UContVar rank copy fml
        fml''  <- liftE $ setCopy ContVar rank copy fml'
        liftE $ setCopy StateVar rank copy fml''

playerToSection :: Player -> Section
playerToSection Existential = ContVar
playerToSection Universal   = UContVar
