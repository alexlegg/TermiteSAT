{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
      synthesise
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either

import Expression.Parse
import Expression.Compile
import Expression.Expression
import Synthesise.Solver

synthesise :: Int -> ParsedSpec -> EitherT String IO Bool
synthesise k spec = evalStateT (synthesise' k spec) emptyManager

synthesise' k spec = do
    let ParsedSpec{..} = spec

    t' <- mapM compile trans
    t <- conjunct t'
    g' <- compile goal
    g <- setRank 0 g'
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
    init <- setRank k init

    checkRank cspec k init

iterateNM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateNM 0 f x = return [x]
iterateNM n f x = do
    fx <- f x
    xs <- iterateNM (n - 1) f fx
    return (x : xs)

