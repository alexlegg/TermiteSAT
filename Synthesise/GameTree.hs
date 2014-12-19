{-# LANGUAGE GADTs, KindSignatures, DataKinds, MultiParamTypeClasses #-}
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
    , gtPlayerMoves
    , gtMove
    , gtState
    , gtPathMoves
    , gtMaxDepth
    , gtChildMoves
    , gtChildren
    , gtMovePairs
    , gtUnsetNodes
    , gtPrevState
    , gtPrevStateGT
    , gtRebase
    , printTree
    , validTree

    -- Modifiers
    , gtNew
    , gtLeaves
    , makePathTree
    , fixPlayerMoves
    , fixInitState
    , projectMoves
    , mergeTrees
    , appendChild
    , appendNextMove
    ) where

import Data.Maybe
import Data.List
import Data.Tuple (swap)
import Utils.Utils
import Expression.Expression
import Expression.Compile
import Expression.AST
import Control.Monad
import qualified Debug.Trace as D

data Player = Existential | Universal deriving (Show, Eq)

opponent Existential    = Universal
opponent Universal      = Existential

instance Show Assignment where
    show (Assignment Pos v) = show v
    show (Assignment Neg v) = '-' : show v

type Move = Maybe [Assignment]

data NodeType = RootNode | InternalNode deriving (Show, Eq)

data Node (t :: NodeType) (p :: Player) where
    U       :: Move -> Move -> [Node InternalNode Existential] -> Node InternalNode Universal
    E       :: Move -> [Node InternalNode Universal] -> Node InternalNode Existential
    SU      :: Move -> [Node InternalNode Existential] -> Node RootNode Universal
    SE      :: Move -> [Node InternalNode Universal] -> Node RootNode Existential

data SNode where
    SNode   :: Node t p -> SNode

class SNodeC (t :: NodeType) (p :: Player) where
    toNode      :: SNode -> Node t p

    viaSNode    :: (SNode -> SNode) -> Node t p -> Node t p
    viaSNode f n = toNode $ f (SNode n)

    mapNodes    :: (SNode -> SNode) -> [Node t p] -> [Node t p]
    mapNodes f = map (viaSNode f)

instance SNodeC InternalNode Universal where
    toNode (SNode u@(U _ _ _))  = u

instance SNodeC RootNode Universal where
    toNode (SNode u@(SU _ _))   = u

instance SNodeC InternalNode Existential where
    toNode (SNode e@(E _ _))    = e

instance SNodeC RootNode Existential where
    toNode (SNode e@(SE _ _))   = e

children :: SNode -> [SNode]
children (SNode (U _ _ cs)) = map SNode cs
children (SNode (E _ cs))   = map SNode cs
children (SNode (SU _ cs))  = map SNode cs
children (SNode (SE _ cs))  = map SNode cs

setChildren :: SNode -> [SNode] -> SNode
setChildren (SNode (U m s _)) cs    = SNode (U m s (map toNode cs))
setChildren (SNode (E m _)) cs      = SNode (E m (map toNode cs))
setChildren (SNode (SU s _)) cs     = SNode (SU s (map toNode cs))
setChildren (SNode (SE s _)) cs     = SNode (SE s (map toNode cs))

snodeMove :: SNode -> Move
snodeMove (SNode (U m _ _))     = m
snodeMove (SNode (E m _))       = m
snodeMove (SNode (SE s _))      = s
snodeMove (SNode (SU s _))      = s

setMove :: Move -> SNode -> SNode
setMove m (SNode (U _ s n'))    = SNode (U m s n')
setMove m (SNode (E _ n'))      = SNode (E m n')
setMove s (SNode (SU _ n'))     = SNode (SU s n')
setMove s (SNode (SE _ n'))     = SNode (SE s n')

snodeState :: SNode -> Move
snodeState (SNode (U _ s _))    = s
snodeState (SNode (E _ _))      = Nothing
snodeState (SNode (SU s _))     = s
snodeState (SNode (SE s _))     = s

data GameTree where
    ETree   :: Int -> [Int] -> Node RootNode Universal -> GameTree
    UTree   :: Int -> [Int] -> Node RootNode Existential -> GameTree

baseRank :: GameTree -> Int
baseRank (ETree r _ _)  = r
baseRank (UTree r _ _)  = r

crumb :: GameTree -> [Int]
crumb (ETree _ c _)     = c
crumb (UTree _ c _)     = c

setCrumb :: GameTree -> [Int] -> GameTree
setCrumb (ETree r c n) c'  = ETree r c' n
setCrumb (UTree r c n) c'  = UTree r c' n

root :: GameTree -> SNode
root (ETree _ _ n)    = SNode n
root (UTree _ _ n)    = SNode n

setRoot :: GameTree -> (SNode -> SNode) -> GameTree
setRoot (ETree r c n) f    = ETree r c (viaSNode f n)
setRoot (UTree r c n) f    = UTree r c (viaSNode f n)

-- |Construct a new game tree for player and rank specified
gtNew :: Player -> Int -> GameTree
gtNew Existential r = ETree r [] (SU Nothing [])
gtNew Universal r   = UTree r [] (SE Nothing [])

-- |Calculates rank of a node (based on base rank)
-- TODO: Needs to be fixed for swapping player order
gtRank :: GameTree -> Int
gtRank (ETree r c _)   = r - (length c `quot` 2)
gtRank (UTree r c _)   = r - (length c `quot` 2)

-- |Returns the root node of the tree
gtBaseRank :: GameTree -> Int
gtBaseRank = baseRank

-- |Returns the first player of the tree (i.e. ETree or UTree)
gtFirstPlayer :: GameTree -> Player
gtFirstPlayer (ETree _ _ _) = Existential
gtFirstPlayer (UTree _ _ _) = Universal

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

-- |Gets the moves for one player
gtPlayerMoves :: Player -> GameTree -> [Move]
gtPlayerMoves p gt = playerNodeMoves p (crumb gt) (root gt)

playerNodeMoves :: Player -> [Int] -> SNode -> [Move]
playerNodeMoves Existential [] (SNode (E m _))      = [m]
playerNodeMoves Existential (c:cs) (SNode (E m ns)) = m : playerNodeMoves Existential cs (SNode (ns !! c))
playerNodeMoves Universal [] (SNode (U m _ _))      = [m]
playerNodeMoves Universal (c:cs) (SNode (U m _ ns)) = m : playerNodeMoves Universal cs (SNode (ns !! c))
playerNodeMoves p [] _                              = []
playerNodeMoves p (c:cs) n                          = playerNodeMoves p cs (children n !! c)

-- |Gets all the states leading to a node
gtStates :: GameTree -> [Move]
gtStates gt = nodeStates (crumb gt) (root gt)

nodeStates :: [Int] -> SNode -> [Move]
nodeStates [] n     = [snodeState n]
nodeStates (c:cs) n = snodeState n : nodeStates cs (children n !! c)

-- |Returns the move at the current node
gtMove :: GameTree -> Move
gtMove = snodeMove . followGTCrumb

gtState :: GameTree -> Move
gtState = snodeState . followGTCrumb

gtPrevState :: GameTree -> Move
gtPrevState gt = snodeState $ followCrumb (root gt) (prevStateNode gt (crumb gt))

gtPrevStateGT :: GameTree -> GameTree
gtPrevStateGT gt = setCrumb gt (prevStateNode gt (crumb gt))

prevStateNode :: GameTree -> [Int] -> [Int]
prevStateNode gt cr = case followCrumb (root gt) cr of
    (SNode (E _ _))     -> init cr
    (SNode (U _ _ _))   -> init (init cr)

-- |Creates a new tree with the current node as its base
gtRebase :: GameTree -> GameTree
gtRebase gt = ETree newrank [] (SU Nothing [(toNode newroot)])
    where
        newcrumb    = alignCrumb (crumb gt)
        newroot     = (followCrumb (root gt) newcrumb)
        newrank     = baseRank gt - (length newcrumb `quot` 2)

-- |Makes a crumb start at the beginning of a step
alignCrumb :: [Int] -> [Int]
alignCrumb cr = take (1 + floor2 (length cr - 1)) cr

-- |Builds a list of trees containing all the leaves of the original tree
gtLeaves :: GameTree -> [GameTree]
gtLeaves gt = map (setCrumb gt) (getLeaves (root gt))

getLeaves :: SNode -> [[Int]]
getLeaves n 
    | null (children n) = [[]]
    | otherwise         = concatMap (\(i, c) -> map (i :) (getLeaves c)) (zip [0..] (children n))

-- |If the GameTree is a single path return the moves
gtPathMoves :: Int -> GameTree -> Maybe [(Move, Move)]
gtPathMoves d gt = Just $ movesToDepth d (root gt)

movesToDepth d n = case children n of
    []      -> [(snodeMove n, snodeState n)]
    (c:[])  -> (snodeMove n, snodeState n) : if d == 0 then [] else movesToDepth (d-1) c

gtMaxDepth :: GameTree -> Int
gtMaxDepth gt = nodeDepth 0 (root gt)

nodeDepth d n = case children n of
    []  -> d+1
    cs  -> maximum $ map (nodeDepth (d+1)) cs

followGTCrumb :: GameTree -> SNode
followGTCrumb gt = followCrumb (root gt) (crumb gt)

followCrumb :: SNode -> [Int] -> SNode
followCrumb r cr = foldl (\n c -> children n !! c) r cr

-- |Gets all outgoing moves of a node
gtChildMoves :: GameTree -> [Move]
gtChildMoves gt = map snodeMove (children (followGTCrumb gt))

gtChildren :: GameTree -> [(Move, GameTree)]
gtChildren gt = zipWith f (children (followGTCrumb gt)) [0..]
    where
        f n i = (snodeMove n, setCrumb gt (crumb gt ++ [i]))

-- |Groups moves by rank
gtMovePairs :: GameTree -> [(Move, Move, Move, Maybe GameTree)]
gtMovePairs gt = case (zip (children n) [0..]) of
    []  -> [(snodeMove n, Nothing, Nothing, Nothing)]
    cs  -> map (\(x, y) -> (snodeMove n, snodeMove x, stateFromPair n x, Just (setCrumb gt (crumb gt ++ [y])))) cs
    where
        n = followGTCrumb gt

stateFromPair :: SNode -> SNode -> Move
stateFromPair (SNode (E _ _)) (SNode (U _ s _)) = s
stateFromPair (SNode (U _ s _)) (SNode (E _ _)) = s

-- |Finds the first Nothing move
gtUnsetNodes :: GameTree -> [GameTree]
gtUnsetNodes gt = map (setCrumb gt) $ filter (not . null) $ map (firstUnsetNode (root gt) 0) (getLeaves (root gt))

firstUnsetNode r cc cr
    | cc == length cr + 1                                   = []
    | isNothing (snodeMove (followCrumb r (take cc cr)))    = take cc cr
    | otherwise                                             = firstUnsetNode r (cc + 1) cr

-- |Filters moves not in the crumb out
makePathTree :: GameTree -> GameTree
makePathTree gt = setCrumb (setRoot gt (makePN (crumb gt))) (replicate (length (crumb gt)) 0)
    where
        makePN :: [Int] -> SNode -> SNode
        makePN [] n = n
        makePN (c:cs) (SNode (E m ns))      = SNode (E m [viaSNode (makePN cs) (ns !! c)])
        makePN (c:cs) (SNode (U m s ns))    = SNode (U m s [viaSNode (makePN cs) (ns !! c)])
        makePN (c:cs) (SNode (SE s ns))     = SNode (SE s [viaSNode (makePN cs) (ns !! c)])
        makePN (c:cs) (SNode (SU s ns))     = SNode (SU s [viaSNode (makePN cs) (ns !! c)])

-- |Fix moves for one player in a path tree only
fixPlayerMoves :: Player -> GameTree -> [([Assignment], [Assignment])] -> GameTree
fixPlayerMoves p gt as = setRoot gt (fpm p as)
    where
        fpm Existential ((m,s):as) (SNode (E _ ns))     = SNode (E (Just m) (mapNodes (fpm p ((m,s):as)) ns))
        fpm Existential ((_,s):as) (SNode (U m _ ns))   = SNode (U m (Just s) (mapNodes (fpm p as) ns))

        fpm Universal ((m,s):as) (SNode (U _ _ ns))     = SNode (U (Just m) (Just s) (mapNodes (fpm p as) ns))
        fpm p as n                                      = setChildren n (map (fpm p as) (children n))

fixInitState :: [Assignment] -> GameTree -> GameTree
fixInitState s gt = setRoot gt fsi
    where
        fsi (SNode (SU _ ns))   = SNode (SU (Just s) ns)
        fsi (SNode (SE _ ns))   = SNode (SE (Just s) ns)

-- |Project moves from one game tree onto another
projectMoves :: GameTree -> GameTree -> Maybe GameTree
projectMoves (ETree r c n) (ETree _ _ pn)   = do
    p <- projectNodes (SNode n) (SNode pn)
    return $ ETree r c (toNode p)
projectMoves (UTree r c n) (UTree _ _ pn)   = do
    p <- projectNodes (SNode n) (SNode pn)
    return $ UTree r c (toNode p)
projectMoves _ _                            = Nothing

projectNodes :: SNode -> SNode -> Maybe SNode
projectNodes (SNode (E m ns))   (SNode (E mp ps))
    | isNothing m   = maybeProject (SNode (E mp [])) ns ps
    | m == mp       = maybeProject (SNode (E m [])) ns ps
    | otherwise     = Nothing
projectNodes (SNode (U m s ns)) (SNode (U mp sp ps))
    | isNothing m   = maybeProject (SNode (U mp sp [])) ns ps
    | m == mp       = maybeProject (SNode (U m sp [])) ns ps
    | otherwise     = Nothing
projectNodes (SNode (SE s ns))  (SNode (SE sp ps))
    | isNothing s   = maybeProject (SNode (SE sp [])) ns ps
    | s == sp       = maybeProject (SNode (SE s [])) ns ps
    | otherwise     = Nothing
projectNodes (SNode (SU s ns))  (SNode (SU sp ps))
    | isNothing s   = maybeProject (SNode (SU sp [])) ns ps
    | s == sp       = maybeProject (SNode (SU s [])) ns ps
    | otherwise     = Nothing

maybeProject :: SNode -> [Node t p] -> [Node t p] -> Maybe SNode
maybeProject s ns ps = do
    ns' <- zipWithM projectNodes (map SNode ns) (map SNode ps)
    return $ setChildren s ns'

mergeTrees :: GameTree -> GameTree -> GameTree
mergeTrees (ETree r c x) (ETree _ _ y) = ETree r [] (toNode (mergeNodes (SNode x) (Just (SNode y))))
mergeTrees (UTree r c x) (UTree _ _ y) = UTree r [] (toNode (mergeNodes (SNode x) (Just (SNode y))))

mergeNodes :: SNode -> Maybe SNode -> SNode
mergeNodes (SNode (E mx xs)) (Just (SNode (E my ys))) = if mx == my
    then SNode $ E mx (map (toNode . uncurry mergeNodes) (zipChildren (map SNode xs) (map SNode ys)))
    else error "Could not merge trees"
mergeNodes (SNode (U mx s xs)) (Just (SNode (U my _ ys))) = if mx == my 
    then SNode $ U mx s (map (toNode . uncurry mergeNodes) (zipChildren (map SNode xs) (map SNode ys)))
    else error "Could not merge trees"
mergeNodes (SNode (SE sx xs)) (Just (SNode (SE sy ys))) = if sx == sy
    then SNode $ SE sx (map (toNode . uncurry mergeNodes) (zipChildren (map SNode xs) (map SNode ys)))
    else error "Could not merge trees"
mergeNodes (SNode (SU sx xs)) (Just (SNode (SU sy ys))) = if sx == sy 
    then SNode $ SU sx (map (toNode . uncurry mergeNodes) (zipChildren (map SNode xs) (map SNode ys)))
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
appendNode m' s' (SNode (SE s ns))  = SNode (SE s (ns ++ [U m' s' []]))
appendNode m' _ (SNode (SU s ns))   = SNode (SU s (ns ++ [E m' []]))

-- |Updates a node in the tree
update :: GameTree -> (SNode -> SNode) -> GameTree
update gt f = setRoot gt (doUpdate f (crumb gt))
    where
        doUpdate :: (SNode -> SNode) -> [Int] -> SNode -> SNode
        doUpdate f [] n     = f n
        doUpdate f (c:cs) n = setChildren n (adjust (doUpdate f cs) c (children n))

-- |Appends the first move in the list that is not already in the tree
appendNextMove :: GameTree -> GameTree -> GameTree
appendNextMove gt cex = setRoot gt (appendMove (baseRank gt * 2) (root cex))

appendMove :: Int -> SNode -> SNode -> SNode
appendMove r cex n
    | null cs   = n
    | null ns   = addNew (snodeMove (head cs)) (snodeState (head cs)) n
    | otherwise = foldl addMove (setChildren n (foldl recur (children n) ms)) nms
    where
        cs                  = children cex
        ns                  = children n
        moveEq x y          = snodeMove x == snodeMove y || snodeMove y == Nothing
        (ms, nms)           = matchIndices moveEq (children cex) (children n)
        recur ys (m, i)     = adjust (appendMove (r-1) m) i ys
        addNew              = if r <= 1 then appendNode else append2Nodes
        addMove x y         = addNew (snodeMove y) (snodeState y) x

matchIndices :: (a -> a -> Bool) -> [a] -> [a] -> ([(a, Int)], [a])
matchIndices _ [] _         = ([], [])
matchIndices f (x:xs) ys    = if isJust m 
    then mapFst (\ps -> ps ++ [(x, fromJust m)]) (matchIndices f xs ys)
    else mapSnd (\ns -> ns ++ [x]) (matchIndices f xs ys)
    where
        m                   = match 0 x ys
        match i a []        = Nothing
        match i a (b:bs)    = if f a b then Just i else match (i+1) a bs

append2Nodes :: Move -> Move -> SNode -> SNode
append2Nodes m' s' (SNode (E m ns))     = SNode (E m (ns ++ [U m' s' [E Nothing []]]))
append2Nodes m' _ (SNode (U m s ns))    = SNode (U m s (ns ++ [E m' [U Nothing Nothing []]]))
append2Nodes m' s' (SNode (SE s ns))    = SNode (SE s (ns ++ [U m' s' [E Nothing []]]))
append2Nodes m' _ (SNode (SU s ns))     = SNode (SU s (ns ++ [E m' [U Nothing Nothing []]]))

printTree :: CompiledSpec -> GameTree -> String
printTree spec gt = "---\n" ++ printNode spec 0 (root gt) ++ "---"

printNode :: CompiledSpec -> Int -> SNode -> String
printNode spec t (SNode (E m cs))    = tab t ++ "E " ++ printMove spec m ++ "\n" ++ concatMap (printNode spec (t+1)) (map SNode cs)
printNode spec t (SNode (U m s cs))  = tab t ++ "U " ++ printMove spec m ++ " | " ++ printMove spec s ++ "\n" ++ concatMap (printNode spec (t+1)) (map SNode cs)
printNode spec t (SNode (SE s cs))   = tab t ++ "SE " ++ printMove spec s ++ "\n" ++ concatMap (printNode spec (t+1)) (map SNode cs)
printNode spec t (SNode (SU s cs))   = tab t ++ "SU " ++ printMove spec s ++ "\n" ++ concatMap (printNode spec (t+1)) (map SNode cs)

tab ind = concat (replicate ind "| ") ++ "|-"

printMove :: CompiledSpec -> Move -> String
printMove spec Nothing   = "Nothing"
printMove spec (Just as) = interMap ", " (printVar spec) vs
    where
        vs = groupBy f as
        f (Assignment _ x) (Assignment _ y) = varname x == varname y

printVar :: CompiledSpec -> [Assignment] -> String
printVar spec as = vname ++ " = " ++ valsToEnums vi vals
    where
        vname   = let (Assignment _ v) = (head as) in varname v
        vi      = fromJust (find (\v -> name v == vname) (vinfo spec))
        vals    = signsToVals 1 [0] (map f [0..(sz vi)-1])
        f b     = fmap sign (find (\(Assignment s v) -> bit v == b) as)

sign (Assignment s _) = s

signsToVals v vs []                   = vs
signsToVals v vs (Nothing: bs)        = signsToVals (v*2) (vs ++ map (+ v) vs) bs
signsToVals v vs ((Just Pos): bs)     = signsToVals (v*2) (map (+ v) vs) bs
signsToVals v vs ((Just Neg): bs)     = signsToVals (v*2) vs bs

valsToEnums VarInfo {enum = Nothing} (v:[])     = show v
valsToEnums VarInfo {enum = Nothing} vs         = show vs
valsToEnums VarInfo {enum = Just eMap} (v:[])   = fromJust (lookup v (map swap eMap))
valsToEnums VarInfo {enum = Just eMap} vs       = "[" ++ interMap ", " (\v -> fromJust (lookup v (map swap eMap))) vs ++ "]"

validTree :: GameTree -> Bool
validTree gt = any ((/= Nothing) . snodeMove) $ map followGTCrumb (gtLeaves gt)
