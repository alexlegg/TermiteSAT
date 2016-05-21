module Synthesise.Config (
      MoveLearning(..)
    , Config(..)
    , SolverType(..)
    , Shortening(..)
    ) where

import Control.Concurrent

data MoveLearning = MLNone | MLFixedMoves FilePath | MLDefaultMoves Int deriving (Show, Eq)

data Shortening = ShortenNone | ShortenExistential | ShortenUniversal | ShortenBoth
    deriving (Show, Eq, Enum)

data SolverType = Unbounded | Bounded Int deriving (Show, Eq)

data Config = Config { tslFile      :: String
                     , solverType   :: SolverType
                     , debugMode    :: Int
                     , moveLearning :: MoveLearning
                     , initMin      :: Maybe Int
                     , shortening   :: Shortening
                     , portfolio    :: Bool
                     , hybrid       :: Bool
                     , hybridMVar   :: Maybe (MVar [[Int]])
                     } deriving (Eq)
