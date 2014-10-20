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

    (s, m) <- runStateT (do {s <- compile init; solveAbstract spec s (GT.empty k)}) emptyManager

    liftIO $ putStrLn (show (satisfiable res))
    liftIO $ putStrLn (show (fromJust $ model res))

    hoistEither $ Right True

solveAbstract spec s gt = do
    findCandidate spec s gt
    return False

findCandidate spec s gt = do
    let ParsedSpec{..} = spec

    let r = GT.rank gt


    t' <- mapM compile trans
    t <- conjunct t'
    g <- compile goal
    u <- compile ucont

    ts  <- iterateNM (r-1) unrollExpression t
    gs  <- iterateNM (r-1) unrollExpression g
    us  <- iterateNM (r-1) unrollExpression u

    liftIO $ putStrLn (show stateVars)

---    vu  <- 
---    vcs <- iterateNM (r-1) 

    liftIO $ putStrLn (show ts)

    return False

iterateNM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateNM 0 f x = return [x]
iterateNM n f x = do
    fx <- f x
    xs <- iterateNM (n - 1) f fx
    return (x : xs)
