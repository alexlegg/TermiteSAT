module Synthesise.GameTree (
      GTNode(..)
    , GTCrumb(..)
    , GameTree(..)
    , Assignment(..)
    , Player(..)
    , opponent
    , gtrank
    , gtcopy
    , gtMoves
    , gtroot
    , gtblocked
    , lastMove
    , blockMove
    , hasChildren
    , empty
    , makeAssignment
    , assignmentToExpression
    , blockingExpression
    , getLeaves
    , appendChild
    , appendChildAt
    , mapChildren
    , mapChildrenM
    ) where

import qualified Data.Map as Map
import Data.Maybe
import Data.List
import Expression.Expression

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

data Player = Existential | Universal deriving (Show, Eq)

opponent Existential    = Universal
opponent Universal      = Existential

instance Show Assignment where
    show (Assignment Pos v) = show v
    show (Assignment Neg v) = '-' : show v

data GTNode = GTNode {
    player      :: Player,
    treerank    :: Int,
    blocked     :: [[Assignment]],
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

gtMoves :: GameTree -> [[Assignment]]
gtMoves = Map.keys . subtrees . follow

gtroot :: GameTree -> GTNode
gtroot (n, _) = n

gtblocked :: GameTree -> [[[Assignment]]]
gtblocked (n, as) = map (\a -> blocked (follow (n, a))) (inits as)

blockMove :: GameTree -> [Assignment] -> GameTree
blockMove gt a = update (\n -> n {blocked = a : (blocked n)}) gt

lastMove :: GameTree -> [Assignment]
lastMove (n, as) = last as

follow :: GameTree -> GTNode
follow (n, [])      = n
follow (n, (a:as))  = follow (fromJust (Map.lookup a (subtrees n)), as)

update :: (GTNode -> GTNode) -> GameTree -> GameTree
update f (n, [])        = (f n, [])
update f (n, (a:as))    = let n' = n {subtrees = Map.adjust (\x -> fst $ update f (x, as)) a (subtrees n)} in (n', a:as)

empty :: Player -> Int -> GameTree
empty p r = (node, []) 
    where node = GTNode {
        player   = p,
        treerank = r,
        blocked  = [],
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
        newrank n   = (treerank n) - if player n == Universal then 1 else 0
        child n     = GTNode {
                        player      = opponent (player n),
                        treerank    = newrank n,
                        blocked     = [],
                        copy        = (copy n) + 1,
                        subtrees    = Map.empty }

appendChildAt :: GameTree -> GTCrumb -> [Assignment] -> GameTree
appendChildAt gt p a = (fst (appendChild (fst gt, p) a), snd gt)

mapChildren :: (GameTree -> a) -> GameTree -> [a]
mapChildren f (gt, as) = map (\a -> f (gt, as ++ [a])) (Map.keys (subtrees gt))

mapChildrenM :: Monad m => (GameTree -> m a) -> GameTree -> m [a]
mapChildrenM f gt = sequence $ mapChildren f gt

assignmentToExpression :: Monad m => [Assignment] -> ExpressionT m Expression
assignmentToExpression as = do
    vs <- mapM f as
    addExpression EConjunct vs
    where
        f (Assignment s v) = do
            e <- addExpression (ELit v) []
            return $ Var s (index e)

blockingExpression :: Monad m => [[Assignment]] -> ExpressionT m (Maybe Expression)
blockingExpression [] = return Nothing
blockingExpression bss = do
    es <- mapM f bss
    e <- conjunct es
    return (Just e)
    where
        f bs = do
            bse <- mapM g bs
            addExpression EDisjunct bse
        g (Assignment s v) = do
            e <- addExpression (ELit v) []
            return $ Var (flipSign s) (index e)
