{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
    synthesise
    ) where

import Expression.Parse
import Expression.Compile
import Expression.Expression
import Debug.Trace
import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map
import SatSolver.SatSolver

initState = ExprManager { maxIndex = 3, exprMap = Map.empty }

synthesise :: ParsedSpec -> EitherT String IO Bool
synthesise spec = do
    let ParsedSpec{..} = spec

    (c, m) <- hoistEither $ runStateT (compile init) initState 

    liftIO $ satSolve 2 [[1], [-2]]

    hoistEither $ Right True
