module Synthesise.GameTree (
    GameTree(..),
    empty
    ) where

import qualified Data.Map as Map

data GameTree = GameTree {
    rank        :: Int,
    children    :: Map.Map String GameTree
    } deriving (Show, Eq)

empty :: Int -> GameTree
empty r = GameTree {
    rank = r,
    children = Map.empty
    }
