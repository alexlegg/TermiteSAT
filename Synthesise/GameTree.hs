module Synthesise.GameTree (
      GameTree
    , Player(..)
    , Assignment(..)
    , Move(..)
    , opponent
    , makeAssignment
    , gtNew
    , gtRank
    , gtBaseRank
    , gtMoves
    , gtMovesFor
    , gtChildMoves
    , gtLeaves
    , assignmentToExpression
    , appendChild
    , appendChildAt
    ) where

import Data.Maybe
import Data.List
import Utils.Utils
import Expression.Expression

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

data Player = Existential | Universal deriving (Show, Eq)

opponent Existential    = Universal
opponent Universal      = Existential

instance Show Assignment where
    show (Assignment Pos v) = show v
    show (Assignment Neg v) = '-' : show v

type Move = Maybe [Assignment]

data GTNode = GTNode {
    childNodes  :: [(Move, GTNode)]
    } deriving (Show, Eq)

data GameTree = GameTree {
    player      :: Player,
    baserank    :: Int,
    root        :: GTNode,
    crumb       :: [Int]
    } deriving (Show, Eq)


-- |Construct a new game tree for player and rank specified
gtNew :: Player -> Int -> GameTree
gtNew p r = GameTree {
      player    = p
    , baserank  = r
    , root      = GTNode { childNodes = [] }
    , crumb     = []
    }

-- |Calculates rank of a node (based on base rank)
-- TODO: Needs to be fixed for swapping player order
gtRank :: GameTree -> Int
gtRank tr = if player tr == Existential
    then baserank tr - (length (crumb tr) `quot` 2)
    else baserank tr - ((length (crumb tr) + 1) `quot` 2)

-- |Returns the root node of the tree
gtBaseRank :: GameTree -> Int
gtBaseRank = baserank

-- |Follows crumb to a node
followCrumb :: GameTree -> GTNode
followCrumb tr = follow (root tr) (crumb tr)
    where
        follow t []     = t
        follow t (c:cs) = follow (snd $ childNodes t !! c) cs

-- |Gets all the moves leading to a node
gtMoves :: GameTree -> [Move]
gtMoves tr = follow (root tr) (crumb tr)
    where
        follow _ []     = []
        follow n (c:cs) = let (m, n') = childNodes n !! c in m : (follow n' cs)

-- |Gets all the moves for a player leading to a node
gtMovesFor :: Player -> GameTree -> [Move]
gtMovesFor p tr 
    | p == Existential && player tr == Existential  = everyEven (gtMoves tr)
    | p == Existential && player tr == Universal    = everyOdd (gtMoves tr)
    | p == Universal && player tr == Existential    = everyOdd (gtMoves tr)
    | p == Universal && player tr == Universal      = everyEven (gtMoves tr)

-- |Gets all outgoing moves of a node
gtChildMoves :: GameTree -> [Move]
gtChildMoves = (map fst) . childNodes . followCrumb

-- |Updates a node in the tree
update :: (GTNode -> GTNode) -> GameTree -> GameTree
update f tr = tr { root = doUpdate f (crumb tr) (root tr) }
    where
        doUpdate f [] n     = f n
        doUpdate f (c:cs) n = n { childNodes = adjust (mapSnd (doUpdate f cs)) c (childNodes n) }


-- |Builds a list of trees containing all the leaves of the original tree
gtLeaves :: GameTree -> [GameTree]
gtLeaves tr = map (\x -> tr {crumb = x}) (getLeaves (root tr))

getLeaves :: GTNode -> [[Int]]
getLeaves gt = if null (childNodes gt)
                then [[]]
                else foldr (\(c, n) x -> (map (c :) (getLeaves n)) ++ x) [] (zip [0..] (map snd (childNodes gt)))

appendChild :: GameTree -> Move -> GameTree
appendChild tr a = update insert tr
    where
        insert g    = g {childNodes = (childNodes g) ++ [(a, child)]}
        child       = GTNode { childNodes = [] }

appendChildAt :: GameTree -> [Int] -> Move -> GameTree
appendChildAt tr c a = tr { root = root (appendChild (tr { crumb = c }) a) }

-- |Contructs an assignment from a model-var pair
makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

-- |Constructs an expression from assignments
assignmentToExpression :: Monad m => [Assignment] -> ExpressionT m Expression
assignmentToExpression as = do
    vs <- mapM f as
    addExpression EConjunct vs
    where
        f (Assignment s v) = do
            e <- addExpression (ELit v) []
            return $ Var s (index e)
