module Synthesise.SolverT (
      SolverT(..)
    , LearnedStates(..)
    , LearningType(..)
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

type SolverST m = StateT LearnedStates m
type SolverT = SolverST (ExpressionT (LoggerT IO))

data LearningType = BoundedLearning | UnboundedLearning deriving (Show, Eq)

data LearnedStates = LearnedStates {
      learningType  :: LearningType
    , winningEx     :: [[Assignment]]
    , winningUn     :: Map.Map Int (Set.Set [Assignment])
    , winningMay    :: [[Assignment]]
    , winningMust   :: [[Assignment]]
}

emptyLearnedStates t = LearnedStates {
      learningType  = t
    , winningEx     = []
    , winningUn     = Map.empty
    , winningMay    = []
    , winningMust   = []
}

throwError :: String -> SolverT a
throwError s = do
    liftLog logDumpLog
    lift (lift (left s))

liftLog :: LoggerT IO a -> SolverT a
liftLog = lift . lift . lift

liftE :: ExpressionT (LoggerT IO) a -> SolverT a
liftE = lift
