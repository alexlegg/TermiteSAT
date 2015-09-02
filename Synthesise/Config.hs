module Synthesise.Config (
      MoveLearning(..)
    , Config(..)
    , Shortening(..)
    ) where

data MoveLearning = MLNone | MLFixedMoves FilePath | MLDefaultMoves Int | MLBadMoves deriving (Show, Eq)

data Shortening = ShortenNone | ShortenExistential | ShortenUniversal | ShortenBoth
    deriving (Show, Eq, Enum)

data Config = Config { tslFile      :: String
                     , bound        :: Maybe Int
                     , debugMode    :: Int
                     , strategyFile :: Maybe FilePath
                     , moveLearning :: MoveLearning
                     , initMin      :: Maybe Int
                     , shortening   :: Shortening
                     } deriving (Show, Eq)
