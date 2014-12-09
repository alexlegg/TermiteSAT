module Synthesise.Strategy (
    computeCounterExample
    ) where

import System.IO
import Control.Monad.State
import Data.Maybe

import Synthesise.GameTree
import Synthesise.GameFormula
import Synthesise.SolverT
import Expression.Expression

computeCounterExample spec player gt = do
    if null (gtUnsetNodes gt)
    then return False
    else do
        let firstUnset = head $ gtUnsetNodes gt
        let gt' = gtPrevStateGT $ firstUnset
        case gtChildMoves gt' of
            (m:[])  -> do
                nextState spec player (gtState gt') firstUnset
            ms      -> do
                liftIO $ putStrLn "multiple moves"
                liftIO $ putStrLn (show ms)
        return $ True

nextState spec player state gt = do
    let gt' = gtRebase gt
    let ((m1, m2, childGT):[]) = concatMap (gtMovePairs . snd) (gtChildren gt')
    liftIO $ putStrLn $ (show m1) ++ " " ++ show m2 ++ "\n" ++ maybe "No child" printTree childGT
    let r = gtRank gt'
    let fp = gtFirstPlayer gt'
    fakes           <- liftE $ trueExpr
    if isJust childGT
    then do
        (next, cMap) <- makeFml spec player fakes (fromJust childGT)
        next' <- liftE $ makePartition next
        fml <- singleStep r spec player fp m1 m2 next

        (dMap, d) <- liftE $ partitionedDimacs fml
        return ()
    else do
        return ()

