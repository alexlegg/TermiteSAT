{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
    synthesise
    ) where

import Debug.Trace
import Data.Maybe
import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map

import Expression.Parse
import Expression.Compile
import Expression.Expression
import qualified Synthesise.GameTree as GT
import SatSolver.SatSolver

initState = ExprManager { maxIndex = 3, exprMap = Map.empty }

synthesise :: Int -> ParsedSpec -> EitherT String IO Bool
synthesise k spec = do
    let ParsedSpec{..} = spec

    (s, m) <- hoistEither $ runStateT (compile init) initState 

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

    solveAbstract spec s (GT.empty k)

    liftIO $ putStrLn (show (satisfiable res))
    liftIO $ putStrLn (show (fromJust $ model res))

    hoistEither $ Right True

solveAbstract spec s gt = do
    hoistEither $ runStateT (findCandidate spec s gt) initState
    return False

findCandidate spec s gt = do
    let ParsedSpec{..} = spec

    mapM_ compile trans

    return False

