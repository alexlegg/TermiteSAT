module Synthesise.Strategy (
    computeCounterExample
    ) where

import Synthesise.GameTree
import System.IO
import Control.Monad.State

computeCounterExample spec player gt = do
    liftIO $ putStrLn "Losing tree"
    liftIO $ putStrLn (printTree gt)
    let gt' = gtPrevStateGT $ head (gtUnsetNodes gt)
    case gtChildMoves gt' of
        (m:[])  -> do
            liftIO $ putStrLn "single move"
            liftIO $ putStrLn (show m)
            nextState spec player gt'
        ms      -> do
            liftIO $ putStrLn "multiple moves"
            liftIO $ putStrLn (show ms)
    return $ True

nextState spec player gt = do
    liftIO $ putStrLn $ "Find the next state"
    liftIO $ putStrLn $ "Start: " ++ show (gtState gt)
    let ((m, c):[]) = gtChildren gt
    liftIO $ putStrLn $ "Play: " ++ show m
    let c' = gtRebase c
    liftIO $ putStrLn (printTree gt)
    liftIO $ putStrLn (printTree c')


