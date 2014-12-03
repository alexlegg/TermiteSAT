{-# LANGUAGE GADTs, KindSignatures, DataKinds #-}
module Synthesise.GameTree (
      GameTree
    , Player(..)
    , Move(..)
    , printMove
    , opponent

    -- Queries on GameTrees
    , gtRank
    , gtRoot
    , gtBaseRank
    , gtFirstPlayer
    , gtCrumb
    , gtMoves
    , gtPathMoves
    , gtChildMoves
    , gtChildren
    , gtMovePairs
    , printTree
    , validTree

    -- Modifiers
    , gtNew
    , gtLeaves
    , makePathTree
    , fixPlayerMoves
    , projectMoves
    , mergeTrees
    , appendChild
    , appendNextMove
    ) where

import Data.Maybe
import Data.List
import Utils.Utils
import Expression.Expression
import Control.Monad

data Player = Existential | Universal deriving (Show, Eq)

opponent Existential    = Universal
opponent Universal      = Existential

instance Show Assignment where
    show (Assignment Pos v) = show v
    show (Assignment Neg v) = '-' : show v

type Move = Maybe [Assignment]

data Node (p :: Player) where
    U       :: Move -> Move -> [Node Existential] -> Node Universal
    E       :: Move -> [Node Universal] -> Node Existential

data SNode where
    SNode   :: Node p -> SNode

class SNodeC (p :: Player) where
    toNode      :: SNode -> Node (p :: Player)

    viaSNode    :: (SNode -> SNode) -> Node (p :: Player) -> Node (p :: Player)
    viaSNode f n = toNode $ f (SNode n)

    mapNodes    :: (SNode -> SNode) -> [Node (p :: Player)] -> [Node (p :: Player)]
    mapNodes f = map (viaSNode f)

instance SNodeC Universal where
    toNode (SNode u@(U _ _ _)) = u

instance SNodeC Existential where
    toNode (SNode e@(E _ _)) = e

children :: SNode -> [SNode]
children (SNode (U _ _ cs))     = map SNode cs
children (SNode (E _ cs))       = map SNode cs

setChildren :: SNode -> [SNode] -> SNode
setChildren (SNode (U m s _)) cs    = SNode (U m s (map toNode cs))
setChildren (SNode (E m _)) cs      = SNode (E m (map toNode cs))

snodeMove :: SNode -> Move
snodeMove (SNode (U m _ _))     = m
snodeMove (SNode (E m _))       = m

setMove :: Move -> SNode -> SNode
setMove m (SNode (U _ s n'))    = SNode (U m s n')
setMove m (SNode (E _ n'))      = SNode (E m n')

data GameTree where
    ETree   :: Int -> [Int] -> Move -> Node Existential -> GameTree
    UTree   :: Int -> [Int] -> Move -> Node Universal -> GameTree

baseRank :: GameTree -> Int
baseRank (ETree r _ _ _)  = r
baseRank (UTree r _ _ _)  = r

crumb :: GameTree -> [Int]
crumb (ETree _ c _ _)     = c
crumb (UTree _ c _ _)     = c

setCrumb :: GameTree -> [Int] -> GameTree
setCrumb (ETree r c s n) c'  = ETree r c' s n
setCrumb (UTree r c s n) c'  = UTree r c' s n

initState :: GameTree -> Move
initState (ETree _ _ s _)   = s
initState (UTree _ _ s _)   = s

root :: GameTree -> SNode
root (ETree _ _ _ n)    = SNode n
root (UTree _ _ _ n)    = SNode n

setRoot :: GameTree -> (SNode -> SNode) -> GameTree
setRoot (ETree r c s n) f    = ETree r c s (viaSNode f n)
setRoot (UTree r c s n) f    = UTree r c s (viaSNode f n)

-- |Construct a new game tree for player and rank specified
gtNew :: Player -> Int -> GameTree
gtNew Existential r = ETree r [] Nothing (E Nothing [])
gtNew Universal r   = UTree r [] Nothing (U Nothing Nothing [])

-- |Calculates rank of a node (based on base rank)
-- TODO: Needs to be fixed for swapping player order
gtRank :: GameTree -> Int
gtRank (ETree r c _ _)   = r - ((length c + 1) `quot` 2)
gtRank (UTree r c _ _)   = r - ((length c + 1) `quot` 2)

-- |Returns the root node of the tree
gtBaseRank :: GameTree -> Int
gtBaseRank = baseRank

-- |Returns the first player of the tree (i.e. ETree or UTree)
gtFirstPlayer :: GameTree -> Player
gtFirstPlayer (ETree _ _ _ _) = Existential
gtFirstPlayer (UTree _ _ _ _) = Universal

gtRoot :: GameTree -> GameTree
gtRoot gt = setCrumb gt []

-- |Returns the crumb for a gametree
gtCrumb :: GameTree -> [Int]
gtCrumb = crumb

-- |Gets all the moves leading to a node
gtMoves :: GameTree -> [Move]
gtMoves gt = nodeMoves (crumb gt) (root gt)

nodeMoves :: [Int] -> SNode -> [Move]
nodeMoves [] n      = [snodeMove n]
nodeMoves (c:cs) n  = snodeMove n : nodeMoves cs (children n !! c)

-- |Builds a list of trees containing all the leaves of the original tree
gtLeaves :: GameTree -> [GameTree]
gtLeaves (ETree r c s n)    = map (\c' -> ETree r c' s n) (getLeaves (SNode n))
gtLeaves (UTree r c s n)    = map (\c' -> UTree r c' s n) (getLeaves (SNode n))

getLeaves :: SNode -> [[Int]]
getLeaves n 
    | null (children n) = [[]]
    | otherwise         = concatMap (\(i, c) -> map (i :) (getLeaves c)) (zip [0..] (children n))

-- |If the GameTree is a single path return the moves
gtPathMoves :: GameTree -> Maybe [Move]
gtPathMoves gt = let leaves = gtLeaves gt in
    if length leaves == 1
    then Just (gtMoves (head leaves))
    else Nothing

followCrumb :: GameTree -> SNode
followCrumb gt = foldl (\n c -> children n !! c) (root gt) (crumb gt)

-- |Gets all outgoing moves of a node
gtChildMoves :: GameTree -> [Move]
gtChildMoves gt = map snodeMove (children (followCrumb gt))

gtChildren :: GameTree -> [(Move, GameTree)]
gtChildren gt = zipWith f (children (followCrumb gt)) [0..]
    where
        f n i = (snodeMove n, setCrumb gt (crumb gt ++ [i]))

-- |Groups moves by rank
gtMovePairs :: GameTree -> [(Move, Move, Maybe GameTree)]
gtMovePairs gt = case gtChildren gt of
    []  -> [(snodeMove (followCrumb gt), Nothing, Nothing)]
    cs  -> map (\(x, y) -> (snodeMove (followCrumb gt), x, Just y)) cs


-- |Filters moves not in the crumb out
makePathTree :: GameTree -> GameTree
makePathTree gt = setCrumb (setRoot gt (makePN (crumb gt))) (replicate (length (crumb gt)) 0)
    where
        makePN :: [Int] -> SNode -> SNode
        makePN [] n = n
        makePN (c:cs) (SNode (E m ns))      = SNode (E m [viaSNode (makePN cs) (ns !! c)])
        makePN (c:cs) (SNode (U m s ns))    = SNode (U m s [viaSNode (makePN cs) (ns !! c)])

-- |Fix moves for one player in a path tree only
fixPlayerMoves :: Player -> GameTree -> [([Assignment], [Assignment])] -> GameTree
fixPlayerMoves p gt as = setRoot gt (fpm p as)
    where
        fpm Existential ((m,_):as) (SNode (E _ ns))     = SNode (E (Just m) (mapNodes (fpm p as) ns))
        fpm Universal ((m,s):as) (SNode (U _ _ ns))     = SNode (U (Just m) (Just s) (mapNodes (fpm p as) ns))
        fpm p as n                                      = setChildren n (map (fpm p as) (children n))

-- |Project moves from one game tree onto another
projectMoves :: GameTree -> GameTree -> Maybe GameTree
projectMoves (ETree r c s n) (ETree _ _ ps pn)  = do
    p <- projectNodes (SNode n) (SNode pn)
    return $ ETree r c ps (toNode p)
projectMoves (UTree r c s n) (UTree _ _ ps pn)  = do
    p <- projectNodes (SNode n) (SNode pn)
    return $ UTree r c ps (toNode p)
projectMoves _ _                            = Nothing

projectNodes :: SNode -> SNode -> Maybe SNode
projectNodes (SNode (E Nothing ns))     (SNode (E mp ps))       = maybeProject (SNode (E mp [])) ns ps
projectNodes (SNode (E m ns))           (SNode (E mp ps))       = if m == mp then maybeProject (SNode (E m [])) ns ps else Nothing
projectNodes (SNode (U Nothing s ns))   (SNode (U mp sp ps))    = maybeProject (SNode (U mp sp [])) ns ps
projectNodes (SNode (U m s ns))         (SNode (U mp sp ps))    = if m == mp then maybeProject (SNode (U m s [])) ns ps else Nothing

maybeProject :: SNode -> [Node p] -> [Node p] -> Maybe SNode
maybeProject s ns ps = do
    ns' <- zipWithM projectNodes (map SNode ns) (map SNode ps)
    return $ setChildren s ns'

mergeTrees :: GameTree -> GameTree -> GameTree
mergeTrees (ETree r c s x) (ETree _ _ _ y) = ETree r [] s (toNode (mergeNodes (SNode x) (Just (SNode y))))
mergeTrees (UTree r c s x) (UTree _ _ _ y) = UTree r [] s (toNode (mergeNodes (SNode x) (Just (SNode y))))

mergeNodes :: SNode -> Maybe SNode -> SNode
mergeNodes (SNode (E mx xs)) (Just (SNode (E my ys))) = if mx == my
    then SNode $ E mx (map (toNode . uncurry mergeNodes) (zipChildren (map SNode xs) (map SNode ys)))
    else error "Could not merge trees"
mergeNodes (SNode (U mx s xs)) (Just (SNode (U my _ ys))) = if mx == my 
    then SNode $ U mx s (map (toNode . uncurry mergeNodes) (zipChildren (map SNode xs) (map SNode ys)))
    else error "Could not merge trees"
mergeNodes n Nothing = n

zipChildren :: [SNode] -> [SNode] -> [(SNode, Maybe SNode)]
zipChildren xs []           = map (\x -> (x, Nothing)) xs
zipChildren [] ys           = map (\y -> (y, Nothing)) ys
zipChildren (x:xs) (y:ys)   = if snodeMove x == snodeMove y
    then (x, Just y) : zipChildren xs ys
    else (x, Nothing) : zipChildren xs (y:ys)

appendChild :: GameTree -> GameTree
appendChild gt = update gt (appendNode Nothing Nothing)

appendNode :: Move -> Move -> SNode -> SNode
appendNode m' s' (SNode (E m ns))   = SNode (E m (ns ++ [U m' s' []]))
appendNode m' _ (SNode (U m s ns))  = SNode (U m s (ns ++ [E m' []]))

-- |Updates a node in the tree
update :: GameTree -> (SNode -> SNode) -> GameTree
update gt f = setRoot gt (doUpdate f (crumb gt))
    where
        doUpdate :: (SNode -> SNode) -> [Int] -> SNode -> SNode
        doUpdate f [] n     = f n
        doUpdate f (c:cs) n = setChildren n (adjust (doUpdate f cs) c (children n))

-- |Appends the first move in the list that is not already in the tree
appendNextMove :: GameTree -> [Move] -> GameTree
appendNextMove gt (m:ms) = setRoot gt (appendMove (baseRank gt * 2) ms)

appendMove :: Int -> [Move] -> SNode -> SNode
appendMove r [] n       = n
appendMove r (m:ms) n 
    | isJust mi         = setChildren n (adjust (appendMove (r-1) ms) (fromJust mi) (children n))
    | otherwise         = if r <= 2 
                            then appendNode m Nothing n 
                            else append2Nodes m Nothing n
    where
        m2n         = zip (map snodeMove (children n)) (children n)
        unsetMove   = lookupIndex Nothing m2n
        mi          = if isJust unsetMove
                        then unsetMove
                        else lookupIndex m m2n

append2Nodes :: Move -> Move -> SNode -> SNode
append2Nodes m' s' (SNode (E m ns))   = SNode (E m (ns ++ [U m' s' [E Nothing []]]))
append2Nodes m' _ (SNode (U m s ns))  = SNode (U m s (ns ++ [E m' [U Nothing Nothing []]]))

printTree :: GameTree -> String
printTree gt = "---\n" ++ "X " ++ printMove (initState gt) ++ "\n" ++ printNode 0 (root gt) ++ "---"

printNode :: Int -> SNode -> String
printNode t (SNode (E m cs))    = tab t ++ "E " ++ printMove m ++ "\n" ++ concatMap (printNode (t+1)) (map SNode cs)
printNode t (SNode (U m s cs))  = tab t ++ "U " ++ printMove m ++ " | " ++ printMove s ++ "\n" ++ concatMap (printNode (t+1)) (map SNode cs)

tab ind = replicate (ind*2) ' '

printMove :: Move -> String
printMove Nothing   = "Nothing"
printMove (Just as) = interMap ", " printVar vs
    where
        vs = groupBy f as
        f (Assignment _ x) (Assignment _ y) = varname x == varname y

printVar :: [Assignment] -> String
printVar as = nm (head as) ++ " = " ++ show (sum (map val as))
    where
        val (Assignment Pos v)  = 2 ^ bit v
        val (Assignment Neg v)  = 0
        nm (Assignment _ v)     = varname v ++ show (rank v)

validTree :: GameTree -> Bool
validTree gt = any ((/= Nothing) . snodeMove) $ map followCrumb (gtLeaves gt)
