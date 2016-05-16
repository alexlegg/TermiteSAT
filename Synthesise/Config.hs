module Synthesise.Config (
      MoveLearning(..)
    , Config(..)
    , SolverType(..)
    , Shortening(..)
    ) where

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
                     } deriving (Show, Eq)
