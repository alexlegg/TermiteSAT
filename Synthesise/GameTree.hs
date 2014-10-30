module Synthesise.GameTree (
      GTNode(..)
    , GTCrumb(..)
    , GameTree(..)
    , Assignment(..)
    , gtrank
    , gtcopy
    , gtroot
    , hasChildren
    , empty
    , makeAssignment
    , assignmentsToExpression
    , getLeaves
    , appendChild
    , appendChildAt
    , mapChildren
    , mapChildrenM
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
    copy        :: Int,
    subtrees    :: Map.Map [Assignment] GTNode
    } deriving (Show, Eq)

type GTCrumb = [[Assignment]]

type GameTree = (GTNode, GTCrumb)

gtrank :: GameTree -> Int
gtrank = treerank . follow

gtcopy :: GameTree -> Int
gtcopy = copy . follow

hasChildren :: GameTree -> Bool
hasChildren = not . Map.null . subtrees . follow

gtroot :: GameTree -> GTNode
gtroot (n, _) = n

follow :: GameTree -> GTNode
follow (n, [])      = n
follow (n, (a:as))  = follow (fromJust (Map.lookup a (subtrees n)), as)

update :: (GTNode -> GTNode) -> GameTree -> GameTree
update f (n, [])        = (f n, [])
update f (n, (a:as))    = let n' = n {subtrees = Map.adjust (\x -> fst $ update f (x, as)) a (subtrees n)} in (n', a:as)

empty :: Int -> GameTree
empty r = (node, []) 
    where node = GTNode {
        treerank = r,
        copy     = 0,
        subtrees = Map.empty
        }

makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

getLeaves :: GameTree -> [GameTree]
getLeaves (gt, c) = map (\x -> (gt, x)) (getLeaves' gt)

getLeaves' :: GTNode -> [GTCrumb]
getLeaves' gt = if Map.null (subtrees gt)
                then [[]]
                else Map.foldWithKey (\c n x -> (map (c :) (getLeaves' n)) ++ x) [] (subtrees gt)

appendChild :: GameTree -> [Assignment] -> GameTree
appendChild gt a = update insert gt
    where
        insert g    = g {subtrees = Map.insert a (child g) (subtrees g)}
        child n     = GTNode {
                        treerank    = (treerank n) - 1,
                        copy        = (copy n) + 1,
                        subtrees    = Map.empty }

appendChildAt :: GameTree -> GTCrumb -> [Assignment] -> GameTree
appendChildAt gt p a = (fst (appendChild (fst gt, p) a), snd gt)

mapChildren :: (GameTree -> a) -> GameTree -> [a]
mapChildren f (gt, as) = map (\a -> f (gt, as ++ [a])) (Map.keys (subtrees gt))

mapChildrenM :: Monad m => (GameTree -> m a) -> GameTree -> m [a]
mapChildrenM f gt = sequence $ mapChildren f gt

assignmentsToExpression :: Monad m => [[Assignment]] -> ExpressionT m Expression
assignmentsToExpression [] = trueExpr
assignmentsToExpression as = do
    vs <- mapM f (concat as)
    addExpression EConjunct vs
    where
        f (Assignment s v) = do
            e <- addExpression (ELit v) []
            return $ Var s (index e)

