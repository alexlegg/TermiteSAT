{-# LANGUAGE RecordWildCards #-}
module Synthesise.Solver (
    checkRank
    ) where

import Data.Maybe
import Data.List
import Data.Tuple.Update
import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Loops
import qualified Data.Map as Map

import Expression.Compile
import Expression.Expression
import Synthesise.GameTree
import SatSolver.SatSolver

checkRank spec rnk s = do
    r <- solveAbstract Existential spec s (empty Existential rnk)
    return (isJust r)

solveAbstract player spec s gt = do
    liftIO $ putStrLn ("Solve abstract for " ++ show player ++ " at rank " ++ show (gtrank gt))
---    liftIO $ putStrLn (show gt)

    cand <- findCandidate player spec s gt

    if isJust cand
    then do
        let gt' = fromJust cand
        cex <- verify player spec s gt'
        if isJust cex
            then do
                let block = lastMove (fromJust cex)
                liftIO $ putStrLn ("CEX at rank " ++ show (gtrank gt) ++ " for " ++ show player ++ ": " ++ (show block))
                let gt'' = blockMove gt block
                solveAbstract player spec s gt''
            else do
                liftIO $ putStrLn ("Verified candidate for " ++ show player ++ "  (rank " ++ show (gtrank gt) ++ ")")
                return cand
    else do
        liftIO $ putStrLn ("Could not find a candidate for " ++ show player ++ " (rank " ++ show (gtrank gt) ++ ")")
        return Nothing

findCandidate player spec s gt = do
    let CompiledSpec{..} = spec
    let r = gtrank gt

    t <- if player == Existential
         then driverFml spec gt
         else environmentFml spec gt

    fml <- conjunct [s, t]
    dimacs <- toDimacs fml
    mi <- getMaxIndex
    res <- liftIO $ satSolve mi dimacs
---    liftIO $ putStrLn ("sat: " ++ (show (satisfiable res)))

    if satisfiable res
    then do
        let m = fromJust (model res)
        let leaves = getLeaves gt
        let saveMove = if player == Existential then saveContMove else saveUContMove
        newchildren <- (liftM catMaybes) (mapM (saveMove spec m) leaves)

        return $ if length newchildren == 0
            then Nothing
            else Just (foldl (\x -> uncurry (appendChildAt x)) gt newchildren)
    else do
        return Nothing

verify player spec s gt = do
    let leaves = filter ((/= 0) . gtrank) (getLeaves gt)
---    liftIO $ putStrLn (show leaves)
    mapMUntilJust (solveAbstract (opponent player) spec s) leaves

mapMUntilJust :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
mapMUntilJust _ []      = return Nothing
mapMUntilJust f (a:as)  = do
    b <- f a
    if isJust b
    then return b
    else mapMUntilJust f as

driverFml spec gt       = makeFml spec gt rootToLeafD

environmentFml spec gt  = makeFml spec gt rootToLeafE

makeFml spec gt rootToLeaf = do
    let rank = treerank (gtroot gt)
    let leaves = getLeaves gt

    base <- rootToLeaf spec rank
    fmls <- mapM (renameAndFix base) leaves
    conjunct fmls

renameAndFix base leaf = do
    let copy = gtcopy leaf

    fr <- setCopy copy base

    m <- assignmentsToExpression (snd leaf)
    mr <- maybe trueExpr (setCopy copy) m

    b <- mapM blockingExpression (gtblocked leaf)
---    liftIO $ putStrLn (show b)
---    bn <- mapM negation (catMaybes b)
    br <- mapM (setCopy copy) (catMaybes b)

    conjunct ([fr, mr] ++ br)

rootToLeafD spec rank = do
    let CompiledSpec{..} = spec

    let i = rank - 1

    goal <- if rank == 1
        then return (g !! i)
        else do
            next <- rootToLeafD spec (rank-1)
            disjunct [next, (g !! i)]

    conjunct [t !! i, vu !! i, vc !! i, goal]

rootToLeafE spec rank = do
    let CompiledSpec{..} = spec

    let i = rank - 1

    goal <- if rank == 1
        then negation (g !! i)
        else do
            ng <- negation (g !! i)
            next <- rootToLeafE spec (rank-1)
            conjunct [next, ng]

    conjunct [t !! i, vu !! i, vc !! i, goal]

saveContMove spec model gt = do
    valid <- isCMoveValid gt spec model
    liftIO $ putStrLn ("Cmove valid? " ++ (show valid))
    if not valid
    then return Nothing
    else do
        move <- saveMove gt model
        let cmove = filter isCont move
        return $ Just (snd gt, cmove)
    where
        isCont (Assignment _ v) = varsect v == ContVar

saveUContMove spec model gt = do
    valid <- isUMoveValid gt spec model
    liftIO $ putStrLn ("Umove valid? " ++ (show valid))
    if not valid
    then return Nothing
    else do
        move <- saveMove gt model
        let umove = filter isUCont move
        return $ Just (snd gt, umove)
    where
        isUCont (Assignment _ v) = varsect v == UContVar

saveMove gt model = do
    let rnk = gtrank gt
    let cpy = gtcopy gt
    exprs <- mapM (lookupExpression . abs) model
    let moves = zipMaybe2 model exprs
    let vmoves = map (mapSnd (getVar . operation)) moves
    let assignments = map makeAssignment ((uncurry zipMaybe2) (unzip vmoves))
    return $ filter (\a -> isRank rnk a && isCopy cpy a) assignments
    where
        getVar (ELit v)  = Just v
        getVar _         = Nothing
        isRank r (Assignment _ v)   = r == (rank v)
        isCopy c (Assignment _ v)   = c == (varcopy v)

isUMoveValid gt spec model = do
    let CompiledSpec{..} = spec
    let r = gtrank gt
    let c = gtcopy gt
    let vuIndex = (map index vu) !! (r - 1)
    vu <- lookupExpression vuIndex
    vuc <- setCopy c (fromJust vu)
    let vuModel = model !! ((index vuc) - 1)
    when ((abs vuModel) /= (index vuc)) (throwError "Assumption about model incorrect")
    return $ vuModel > 0

isCMoveValid gt spec model = do
    let CompiledSpec{..} = spec
    let r = gtrank gt
    let c = gtcopy gt
    let vcIndex = (map index vc) !! (r - 1)
    vc <- lookupExpression vcIndex
    vcc <- setCopy c (fromJust vc)
    let vcModel = model !! ((index vcc) - 1)
    when ((abs vcModel) /= (index vcc)) (throwError "Assumption about model incorrect")
    return $ vcModel > 0

zipMaybe2 :: [a] -> [Maybe b] -> [(a, b)]
zipMaybe2 as bs = mapMaybe f (zip as bs)
    where
    f (a, b) = do
        b' <- b
        return (a, b')

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (x,y) = (f x,y)

mapSnd :: (a -> b) -> (c, a) -> (c, b)
mapSnd f (x,y) = (x,f y)

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . left
