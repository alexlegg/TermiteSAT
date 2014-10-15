{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
    synthesise
    ) where

import Expression.Parse
import Expression.Compile
import Expression.Expression
import Debug.Trace
import Data.Maybe
import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map
import SatSolver.SatSolver

initState = ExprManager { maxIndex = 3, exprMap = Map.empty }

synthesise :: ParsedSpec -> EitherT String IO Bool
synthesise spec = do
    let ParsedSpec{..} = spec

    (c, m) <- hoistEither $ runStateT (compile init) initState 

    res <- liftIO $ satSolve 5 [
        [-3, 1],
        [-3, -2],
        [3, -1, 2],
        [-4, -1],
        [-4, 2],
        [4, 1, -2],
        [-5, 3, 4],
        [5, -3],
        [5, -4],
        [5]
        ]

    liftIO $ putStrLn (show (satisfiable res))
    liftIO $ putStrLn (show (fromJust $ model res))

    hoistEither $ Right True
