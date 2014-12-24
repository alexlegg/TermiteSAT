{-# LANGUAGE RecordWildCards #-}
module Synthesise.GameFormula (
      makeFml
    , singleStep
    , groupCrumb
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
    liftE $ clearCopies
    initMove    <- liftE $ moveToExpression (gtMove root)
    s'          <- liftE $ maybeM s (\i -> conjunct [s, i]) initMove

    if null (gtChildren root)
    then do
        fml         <- leafToBottom spec player rank
        fml'        <- liftE $ conjunct [fml, s']

        return (fml', [])
    else do
        let cs      = map (gtMovePairs . snd) (gtChildren root)
        steps       <- mapM (mapM (makeStep rank spec player (gtFirstPlayer gt))) cs
        (fml, cMap) <- mergeRenamed player (gtFirstPlayer gt) spec rank (map (map fth4) cs) (map (map fst) steps)
        fml'        <- liftE $ conjunct [fml, s']
        return (fml', cMap ++ concatMap (concatMap snd) steps)

mergeRenamed player fp spec rank (gt:[]) (f:[])
    | length gt == 1    = return (head f, [])
    | otherwise         = mergeSharedMove player fp spec rank gt f
mergeRenamed player fp spec rank (gt:gts) (f:fs) = do
    let dontRename  = map (setVarRank rank) (svars spec)

    (ffml, cMaps)   <- mergeSharedMove player fp spec rank gt f
    (fmls, cMaps')  <- unzipM $ zipWithM (mergeSharedMove player fp spec rank) gts fs
    (cpy, cfmls)    <- unzipM $ liftE $ mapM (makeCopy dontRename) fmls
    fml             <- liftE $ conjunct (ffml : cfmls)

    return (fml, cMaps  ++ concat cMaps')

makeCMap gt copyId = (groupCrumb (gtCrumb gt), copyId)

mergeSharedMove player fp spec rank gts fs = do
    let statevars   = map (setVarRank rank) (svars spec)
    let movevars    = if player == Existential
                        then map (setVarRank rank) (cont spec)
                        else map (setVarRank rank) (ucont spec)
    let dontRename  = statevars ++ (if player == fp then movevars else [])

    (copies, fs')   <- liftE $ unzipM (mapM (makeCopy dontRename) fs)
    fml             <- liftE $ conjunct fs'

    let cMap = zipMaybe1 (map (fmap (groupCrumb . gtCrumb)) gts) copies
    return (fml, cMap)

makeStep rank spec player first (m1, m2, s, c) = do
    let CompiledSpec{..} = spec
    let i = rank - 1

    (next, cmap) <- if isJust c
        then do
            let cs = map (gtMovePairs . snd) (gtChildren (fromJust c))
            if null cs
            then do
                f <- leafToBottom spec player (rank-1)
                return (f, [])
            else do
                steps <- mapM (mapM (makeStep (rank-1) spec player first)) cs
                (f, cMap') <- mergeRenamed player first spec (rank-1) (map (map fth4) cs) (map (map fst) steps)
                return (f, concatMap (concatMap snd) steps ++ cMap')
        else do
            f <- leafToBottom spec player (rank-1)
            return (f, [])

    g' <- liftE $ goalFor player (g !! i)
    goal <- if player == Existential
        then liftE $ disjunct [next, g']
        else liftE $ conjunct [next, g']

    step    <- singleStep rank spec player first m1 m2 s
    f       <- liftE $ conjunct [step, goal]
    return (f, cmap)

singleStep rank spec player first m1 m2 s = do
    let CompiledSpec{..} = spec
    let i   = rank - 1
    let vh  = if player == Existential then vu else vc

    m1' <- if player == first
        then liftE $ moveToExpression m1
        else liftE $ makeHatMove (vh !! i) m1

    m2' <- if player == first
        then liftE $ makeHatMove (vh !! i) m2
        else liftE $ moveToExpression m2

    block <- blockLosingStates rank player

    let moves = catMaybes [m1', m2', block]
    liftE $ conjunct ([t !! i, vu !! i, vc !! i] ++ moves)

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

leafToBottom :: CompiledSpec -> Player -> Int -> SolverT Expression
leafToBottom spec player rank = do
    let CompiledSpec{..} = spec
    let i = rank - 1

    when (rank < 0) $ throwError "leafToBottom called on a tree that's too long"

    if rank == 0
    then liftE $ goalFor player (g !! 0)
    else do
        goal <- if rank == 1
            then liftE $ goalFor player (g !! i)
            else do
                next <- leafToBottom spec player (rank-1)
                g' <- liftE $ goalFor player (g !! i)
                if player == Existential
                    then liftE $ disjunct [next, g']
                    else liftE $ conjunct [next, g']

        block <- blockLosingStates rank player
        if isJust block
        then liftE $ conjunct [t !! i, vu !! i, vc !! i, goal, fromJust block]
        else liftE $ conjunct [t !! i, vu !! i, vc !! i, goal]

groupCrumb []          = []
groupCrumb (m1:[])     = [(m1,0)]
groupCrumb (m1:m2:ms)  = (m1,m2) : groupCrumb ms

