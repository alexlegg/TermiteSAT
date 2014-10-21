module Synthesise.GameTree (
      GameTree(..)
    , empty
    , newChild
    ) where

import qualified Data.Map as Map
import Expression.Expression

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

instance Show Assignment where
    show (Assignment Pos v) = show v
    show (Assignment Neg v) = '-' : show v

data GameTree = GameTree {
    treerank    :: Int,
    subtrees    :: Map.Map [Assignment] GameTree
    } deriving (Show, Eq)

empty :: Int -> GameTree
empty r = GameTree {
    treerank = r,
    subtrees = Map.empty
    }

newChild :: GameTree -> [(Int, ExprVar)] -> GameTree
newChild root es = root {subtrees = newsubtrees}
    where
        assignment  = map (\(m, e) -> Assignment (if m > 0 then Pos else Neg) e) es
        newnode     = empty ((treerank root) - 1)
        newsubtrees = Map.insert assignment newnode (subtrees root)
