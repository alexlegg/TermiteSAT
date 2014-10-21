{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
    synthesise
    ) where

import Debug.Trace
import Data.Maybe
import Data.List
import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map

import Expression.Parse
import Expression.Compile
import Expression.Expression
import qualified Synthesise.GameTree as GT
import SatSolver.SatSolver

data CompiledSpec = CompiledSpec {
      t       :: [Expression]
    , g       :: [Expression]
    , u       :: [Expression]
    , vc      :: [Expression]
    , vu      :: [Expression]
    }
    

synthesise :: Int -> ParsedSpec -> EitherT String IO Bool
synthesise k spec = evalStateT (synthesise' k spec) emptyManager

synthesise' k spec = do
    let ParsedSpec{..} = spec

    t' <- mapM compile trans
    t <- conjunct t'
    g <- compile goal
    u <- compile ucont

    let xvars = map compileVar stateVars
    let uvars = map compileVar ucontVars
    let cvars = map compileVar contVars

    u_idle <- equalsConstant (concat uvars) 0
    c_idle <- equalsConstant (concat cvars) 0

    vc <- equate c_idle u
    vu <- implicate u =<< (negation u_idle)

    ts  <- iterateNM (k-1) unrollExpression t
    gs  <- iterateNM (k-1) unrollExpression g
    us  <- iterateNM (k-1) unrollExpression u
    vcs <- iterateNM (k-1) unrollExpression vc
    vus <- iterateNM (k-1) unrollExpression vu

    let cspec = CompiledSpec {
          t     = ts
        , g     = gs
        , u     = us
        , vc    = vcs
        , vu    = vus
        }

    init <- compile init
    solveAbstract cspec init (GT.empty k)

solveAbstract spec s gt = do
    findCandidate spec s gt
    return False

findCandidate spec s gt = do
    let CompiledSpec{..} = spec
    let r = GT.rank gt

    d <- driverFml spec (r-1)

    dimacs <- toDimacs d
    mi <- getMaxIndex
    res <- liftIO $ satSolve mi dimacs

    move <- if satisfiable res
            then do
                let m = fromJust (model res)
                exprs <- mapM (lookupExpression . abs) m
                let f (m, x) = if isJust x
                               then case operation (fromJust x) of
                                    ELit v      -> Just $ (if m > 0 then '+' else '-') : (show v)
                                    _           -> Nothing
                               else Nothing

                return $ intercalate " " (catMaybes (map f (zip m exprs)))
            else
                return []

    liftIO $ putStrLn (show move)

    return False

driverFml spec rank = do
    let CompiledSpec{..} = spec
    prev <- if rank == 0
        then trueExpr
        else driverFml spec (rank - 1)

    goal <- disjunct [(g !! rank), prev]
    conjunct [t !! rank, vc !! rank, vu !! rank, goal]

iterateNM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateNM 0 f x = return [x]
iterateNM n f x = do
    fx <- f x
    xs <- iterateNM (n - 1) f fx
    return (x : xs)
