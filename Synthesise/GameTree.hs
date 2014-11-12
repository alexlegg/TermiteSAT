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
    , gtChildMoves
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

data GTNode = GTNode {
    player      :: Player,
    treerank    :: Int,
    blocked     :: [[Assignment]],
    copy        :: Int,
    subtrees    :: [([Assignment], GTNode)]
    } deriving (Show, Eq)

type GTCrumb = [Int]

type GameTree = (GTNode, GTCrumb)

gtrank :: GameTree -> Int
gtrank = treerank . follow

gtcopy :: GameTree -> Int
gtcopy = copy . follow

hasChildren :: GameTree -> Bool
hasChildren = not . null . subtrees . follow

-- Gets all outgoing moves of a node
gtChildMoves :: GameTree -> [[Assignment]]
gtChildMoves = (map fst) . subtrees . follow

-- Gets all the moves leading to a node
gtMoves :: GameTree -> [[Assignment]]
gtMoves (_, [])     = []
gtMoves (n, a:as)   = let c = subtrees n !! a in fst c : (gtMoves (snd c, as))

gtroot :: GameTree -> GTNode
gtroot (n, _) = n

gtblocked :: GameTree -> [[[Assignment]]]
gtblocked (n, as) = map (\a -> blocked (follow (n, a))) (inits as)

blockMove :: GameTree -> [Assignment] -> GameTree
blockMove gt a = update (\n -> n {blocked = a : (blocked n)}) gt

lastMove :: GameTree -> [Assignment]
lastMove (n, as) = fst ((subtrees prev) !! (last as))
    where
        prev = follow (n, init as)

follow :: GameTree -> GTNode
follow (n, [])      = n
follow (n, (a:as))  = follow (snd ((subtrees n) !! a), as)

update :: (GTNode -> GTNode) -> GameTree -> GameTree
update f (n, [])        = (f n, [])
update f (n, (a:as))    = let n' = n {subtrees = adjust (\x -> (fst x, fst $ update f (snd x, as))) a (subtrees n)} in (n', a:as)

empty :: Player -> Int -> GameTree
empty p r = (node, []) 
    where node = GTNode {
        player   = p,
        treerank = r,
        blocked  = [],
        copy     = 0,
        subtrees = []
        }

makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

getLeaves :: GameTree -> [GameTree]
getLeaves (gt, c) = map (\x -> (gt, x)) (getLeaves' gt)

getLeaves' :: GTNode -> [GTCrumb]
getLeaves' gt = if null (subtrees gt)
                then [[]]
                else foldr (\(c, n) x -> (map (c :) (getLeaves' n)) ++ x) [] (zip [0..] (map snd (subtrees gt)))

appendChild :: GameTree -> [Assignment] -> GameTree
appendChild gt a = update insert gt
    where
        insert g    = g {subtrees = (subtrees g) ++ [(a, (child g))]}
        newrank n   = (treerank n) - if player n == Universal then 1 else 0
        child n     = GTNode {
                        player      = opponent (player n),
                        treerank    = newrank n,
                        blocked     = [],
                        copy        = (copy n) + 1,
                        subtrees    = [] }

appendChildAt :: GameTree -> GTCrumb -> [Assignment] -> GameTree
appendChildAt gt p a = (fst (appendChild (fst gt, p) a), snd gt)

mapChildren :: (GameTree -> a) -> GameTree -> [a]
mapChildren f (gt, as) = map (\a -> f (gt, as ++ [a])) [0 .. length (subtrees gt)]

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
