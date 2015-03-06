module Synthesise.SolverT (
      SolverT(..)
    , LearnedStates(..)
    , emptyLearnedStates
    , throwError
    , liftLog
    , liftE
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import Expression.Expression
import Utils.Logger
import SatSolver.Interpolator

type SolverST m = StateT LearnedStates m
type SolverT = SolverST (InterpolatorST (ExpressionT (LoggerT IO)))

data LearnedStates = LearnedStates {
      winningEx :: [[Assignment]]
    , winningUn :: Map.Map Int (Set.Set [Assignment])
}

emptyLearnedStates = LearnedStates {
      winningEx = []
    , winningUn = Map.empty
}

throwError :: String -> SolverT a
throwError s = do
    liftLog logDumpLog
    lift (lift (lift (left s)))

liftLog :: LoggerT IO a -> SolverT a
liftLog = lift . lift . lift . lift

liftE :: ExpressionT (LoggerT IO) a -> SolverT a
liftE = lift . lift
