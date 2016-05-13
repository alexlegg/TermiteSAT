module Synthesise.SolverT (
      SolverT
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
      learningType      :: LearningType
    , winningMust       :: Set.Set (Set.Set Assignment)
    , winningMay        :: Map.Map Int (Set.Set (Set.Set Assignment))
    , defaultUnMoves    :: Map.Map Int [Assignment]
    , defaultExMoves    :: Map.Map Int [Assignment]
    , badMovesUn        :: Set.Set [Assignment]
    , badMovesEx        :: Set.Set (Int, [Assignment])
    , checkedMoves      :: Set.Set (Int, [Assignment], [Assignment])
}

emptyLearnedStates :: LearningType -> LearnedStates
emptyLearnedStates t = LearnedStates {
      learningType      = t
    , winningMust       = Set.empty
    , winningMay        = Map.empty
    , defaultUnMoves    = Map.empty
    , defaultExMoves    = Map.empty
    , badMovesUn        = Set.empty
    , badMovesEx        = Set.empty
    , checkedMoves      = Set.empty
}

throwError :: String -> SolverT a
throwError s = do
    liftLog $ logDumpLog
    lift (lift (left ("ERROR: " ++ s)))

liftLog :: LoggerT IO a -> SolverT a
liftLog = lift . lift . lift

liftE :: ExpressionT (LoggerT IO) a -> SolverT a
liftE = lift
