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

synthesise :: Int -> ParsedSpec -> EitherT String IO Bool
synthesise k spec = do
    let ParsedSpec{..} = spec

    (s, m) <- runStateT (compile init) emptyManager

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
    runStateT (findCandidate spec s gt) emptyManager
    return False

findCandidate spec s gt = do
    let ParsedSpec{..} = spec

    t' <- mapM compile trans
    t <- conjunct t'

    m <- get
---    liftIO $ putStrLn (show m)
    liftIO $ putStrLn (show t)

    return False

