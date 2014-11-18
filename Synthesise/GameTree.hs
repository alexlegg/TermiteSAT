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
    , gtCrumb
    , gtMoves
    , gtPathMoves
    , gtMovesFor
    , gtChildMoves
    , gtLeaves
    , makePathTree
    , fixMoves
    , fixPlayerMoves
    , mergeTrees
    , assignmentToExpression
    , appendChild
    , appendChildAt
    , appendNextMove
    , printTree
    ) where

import Data.Maybe
import Data.List
import Utils.Utils
import Expression.Expression
import Debug.Trace

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


-- |Gives an empty GameTree node
emptyNode :: GTNode
emptyNode = GTNode { childNodes = [] }

-- |Construct a new game tree for player and rank specified
gtNew :: Player -> Int -> GameTree
gtNew p r = GameTree {
      player    = p
    , baserank  = r
    , root      = emptyNode
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

-- |Returns the crumb for a gametree
gtCrumb :: GameTree -> [Int]
gtCrumb = crumb

-- |Gets all the moves leading to a node
gtMoves :: GameTree -> [Move]
gtMoves tr = follow (root tr) (crumb tr)
    where
        follow _ []     = []
        follow n (c:cs) = let (m, n') = childNodes n !! c in m : (follow n' cs)

-- |If the GameTree is a single path return the moves
gtPathMoves :: GameTree -> Maybe [Move]
gtPathMoves gt = let leaves = gtLeaves gt in
    if length leaves == 1
    then Just (gtMoves (head leaves))
    else Nothing

-- |Gets all the moves for a player leading to a node
gtMovesFor :: Player -> GameTree -> [Move]
gtMovesFor p tr 
    | p == Existential && player tr == Existential  = everyOdd (gtMoves tr)
    | p == Universal && player tr == Existential    = everyEven (gtMoves tr)
    | p == Existential && player tr == Universal    = everyOdd (gtMoves tr)
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

-- |Filters moves not in the crumb out
makePathTree :: GameTree -> GameTree
makePathTree gt = gt { root = makePathNodes (root gt) (crumb gt), crumb = replicate (length (crumb gt)) 0 }

makePathNodes n []      = n
makePathNodes n (c:cs)  = let (m, n') = (childNodes n) !! c in n { childNodes = [(m, makePathNodes n' cs)] }

-- |Fix moves in a GameTree (ignores crumb)
fixMoves :: GameTree -> [[Assignment]] -> GameTree
fixMoves gt as = gt { root = fixMoveNode as (root gt) }

fixMoveNode [] n        = n
fixMoveNode (a:as) n    = let n' = findIndex (\x -> Just a == fst x) (childNodes n) in
    if isJust n'
    then n { childNodes = adjust (mapSnd (fixMoveNode as)) (fromJust n') (childNodes n) }
    else n { childNodes = childNodes n ++ [(Just a, fixMoveNode as emptyNode)] }

-- |Fix moves for one player in a path tree only
fixPlayerMoves :: Player -> GameTree -> [[Assignment]] -> GameTree
fixPlayerMoves p gt as
    | player gt == p  = gt { root = fpmSet (root gt) as }
    | player gt /= p  = gt { root = fpmSkip (root gt) as }

fpmSkip n [] = n
fpmSkip n as
    | null (childNodes n) = n
    | otherwise           = let (m, n') = head (childNodes n) in n { childNodes = [(m, fpmSet n' as)] }

fpmSet n [] = n
fpmSet n (a:as)
    | null (childNodes n) = n { childNodes = [(Just a, emptyNode)] }
    | otherwise           = let (_, n') = head (childNodes n) in n { childNodes = [(Just a, fpmSkip n' as)] }

mergeTrees :: GameTree -> GameTree -> GameTree
mergeTrees x y = if player x == player y && baserank x == baserank y
                    then x { root = mergeNodes (root x) (root y), crumb = [] }
                    else error $ "Could not merge trees"

mergeNodes :: GTNode -> GTNode -> GTNode
mergeNodes x y = emptyNode { childNodes = foldl f (childNodes x) (childNodes y) }
    where
        f cs (m, y) = let i = lookupIndex m cs in
            if isJust i
            then adjust (\(move, x) -> (move, mergeNodes x y)) (fromJust i) cs
            else cs ++ [(m, y)]

appendChild :: GameTree -> Move -> GameTree
appendChild tr a = update insert tr
    where
        insert g    = g {childNodes = (childNodes g) ++ [(a, child)]}
        child       = GTNode { childNodes = [] }

appendChildAt :: GameTree -> [Int] -> Move -> GameTree
appendChildAt tr c a = tr { root = root (appendChild (tr { crumb = c }) a) }

appendNextMove :: GameTree -> [Move] -> GameTree
appendNextMove gt ms = gt { root = appendNextMove' ms (root gt) }

appendNextMove' [] n = n
appendNextMove' (m:ms) n
    | null (childNodes n)   = n { childNodes = [(m, GTNode { childNodes = [(Nothing, emptyNode)] } )] }
    | isJust mi             = n { childNodes = adjust (mapSnd (appendNextMove' ms)) (fromJust mi) (childNodes n) }
    | otherwise             = n { childNodes = childNodes n ++ [(m, GTNode { childNodes = [(Nothing, emptyNode)] } )] }
    where
        mi = lookupIndex m (childNodes n)

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

printTree :: GameTree -> String
printTree gt = "---\n" ++ printNode (root gt) 0 ++ "---"

printNode n ind = concatMap printChildren (childNodes n)
    where
        printChildren (m, n') = (replicate (ind*2) ' ') ++ show m ++ "\n" ++ printNode n' (ind+1)
