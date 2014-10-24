module Synthesise.GameTree (
      GTNode(..)
    , GTCrumb(..)
    , GameTree(..)
    , Assignment(..)
    , gtrank
    , empty
    , makeAssignment
    , mapLeaves
    ) where

import qualified Data.Map as Map
import Data.Maybe
import Expression.Expression

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

instance Show Assignment where
    show (Assignment Pos v) = show v
    show (Assignment Neg v) = '-' : show v

data GTNode = GTNode {
    treerank    :: Int,
    subtrees    :: Map.Map [Assignment] GTNode
    } deriving (Show, Eq)

type GTCrumb = [[Assignment]]

type GameTree = (GTNode, GTCrumb)

gtrank :: GameTree -> Int
gtrank = treerank . follow

follow (n, [])      = n
follow (n, (a:as))  = follow (fromJust (Map.lookup a (subtrees n)), as)

empty :: Int -> GameTree
empty r = (node, []) 
    where node = GTNode {
        treerank = r,
        subtrees = Map.empty
        }

makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

mapLeaves :: (GTNode -> a) -> GTNode -> [a]
mapLeaves f gt = if Map.null (subtrees gt)
                 then [f gt]
                 else concat $ Map.elems (Map.map (mapLeaves f) (subtrees gt))
