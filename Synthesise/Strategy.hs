module Synthesise.Strategy (
    computeCounterExample
    ) where

import Synthesise.GameTree
import System.IO
import Control.Monad.State

computeCounterExample gt = do
    liftIO $ putStrLn "Losing tree"
    let gt' = gtPrevStateGT $ head (gtUnsetNodes gt)
    liftIO $ putStrLn (show (gtChildMoves gt'))
    liftIO $ putStrLn (printTree gt')
    return $ True
