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
    let maxCopy = gtMaxCopy gt

    block <- makeBlockingExpressions player rank maxCopy
---    when (maxCopy /= 0) $ do
---        liftIO $ putStrLn $ (show player) ++ " " ++ show rank
---        blockp <- liftE $ mapM printExpression block
---        liftIO $ mapM putStrLn blockp
---        throwError "stop"

    if null (gtChildren root)
    then do
        fml         <- leafToBottom spec 0 (gtFirstPlayer gt) player rank
        fml'        <- liftE $ conjunct (fml : s' : block)

        return fml'
    else do
        let cs      = map gtMovePairs (gtChildren root)
        steps       <- concatMapM (mapM (makeSteps rank spec player (gtFirstPlayer gt) root)) cs
        moves       <- concatMapM (concatMapM (makeMoves rank spec player (gtFirstPlayer gt) root)) cs

        fml'        <- liftE $ conjunct (s' : block ++ (catMaybes moves) ++ steps)
        return fml'

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

makeSteps rank spec player first gt (m1, m2, c) = do
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
                steps <- concatMapM (mapM (makeSteps (rank-1) spec player first (fromJust c))) cs
                liftE $ conjunct steps
        else do
            leafToBottom spec (gtCopyId gt) first player (rank-1)

    singleStep spec rank first player parentCopy copy1 copy2 next

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
            let cMap = Map.fromList [
                          ((playerToSection first, rank), copy1)
                        , ((playerToSection (opponent first), rank), copy2)
                        , ((StateVar, rank-1), copy2)
                        , ((StateVar, rank), parentCopy)
                        ]
            step    <- liftE $ setCopyStep cMap (t !! i)
            liftE $ cacheStep (rank, parentCopy, copy1, copy2, exprIndex (t !! i)) step
            return step

    liftE $ conjunct [step, goal]

makeBlockingExpressions :: Player -> Int -> Int -> SolverT [Expression]
makeBlockingExpressions player rank copy = do
    LearnedStates{..} <- get
    let blah = [(r, c) | r <- [0..rank], c <- [0..copy]]
    if player == Existential
        then do
            concatMapM (makeBlockEx winningUn) (concatMap (\r -> map (\c -> (r, c)) [0..copy]) [0..rank])
        else do
            concatMapM (\(r, c) -> blockExpression winningEx r c) blah

blockExpression as rank copy = do
    let ass = map (map (\a -> setAssignmentRankCopy a rank copy)) as
    liftE $ mapM blockAssignment ass

makeBlockEx blocking (rank, copy) = do
    let as = fromMaybe [] (Map.lookup rank blocking)
    blockExpression as rank copy

---getCacheOrCopy es copy = do
---    mapM (setCopyAll copy) es
---    mapM doCopies es
---    where
---        doCopies e = do
---            cache <- getCached (0, copy, copy, copy, exprIndex e)
---            if isJust cache
---            then return (fromJust cache)
---            else do
---                ce <- setCopyAll copy e
---                cacheStep (0, copy, copy, copy, exprIndex e) ce
---                return ce

makeMoveExpression Nothing _ _          = return Nothing
makeMoveExpression (Just a) hat vars    = do
    cached <- getCachedMove (a, hat)
    case cached of
        (Just m)    -> return (Just m)
        Nothing     -> do
            move <- if hat
                then assignmentToExpression a
                else makeHatMove vars a
            cacheMove (a, hat) move
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
