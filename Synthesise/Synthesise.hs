{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
      synthesise
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Data.Maybe

import Utils.Logger
import Expression.Parse
import Expression.Compile
import Expression.Expression
import Synthesise.Solver
import Expression.AST

synthesise :: Int -> ParsedSpec -> EitherT String (LoggerT IO) Bool
synthesise k spec = evalStateT (synthesise' k spec) emptyManager

enumValidity vi@(VarInfo {enum = Nothing}) = return Nothing
enumValidity vi@(VarInfo {enum = Just es}) = do
    let vars = compileVar vi
    let invalid = [(length es)..((2 ^ sz vi)-1)]
    eqs <- mapM ((negation =<<) . equalsConstant vars) invalid
    c <- conjunct eqs
    c' <- setRank 1 c
    return (Just c')

synthesise' k spec = do
    let ParsedSpec{..} = spec

    t' <- mapM compile trans
    t <- conjunct t'
    g' <- compile goal
    g <- setRank 0 g'
    u <- compile ucont

    let svars = concatMap compileVar stateVars
    let uvars = concatMap compileVar ucontVars
    let cvars = concatMap compileVar contVars

    let vinfo = stateVars ++ ucontVars ++ contVars

    u_idle <- equalsConstant (map (\v -> v {rank = 1}) uvars) 0
    c_idle <- equalsConstant (map (\v -> v {rank = 1}) cvars) 0

    cev <- mapM enumValidity contVars
    uev <- mapM enumValidity ucontVars

    vc' <- equate c_idle u
    vc  <- conjunct (vc' : catMaybes cev)
    vu' <- implicate u =<< (negation u_idle)
    vu  <- conjunct (vu' : catMaybes uev)

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
        , cont  = cvars
        , ucont = uvars
        , svars = svars
        , vinfo = vinfo
        }

    lift $ lift $ logSpec cspec

    init <- compile init
    init <- setRank k init

    evalStateT (checkRank cspec k init) emptyLearnedStates

iterateNM :: Monad m => Int -> (a -> m a) -> a -> m [a]
iterateNM 0 f x = return [x]
iterateNM n f x = do
    fx <- f x
    xs <- iterateNM (n - 1) f fx
    return (x : xs)

