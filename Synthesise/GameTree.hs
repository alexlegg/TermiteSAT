{-# LANGUAGE GADTs, KindSignatures, DataKinds, MultiParamTypeClasses, RecordWildCards #-}
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
    , gtCopyId
    , gtCopies
    , gtParent
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
    U       :: Int -> Move -> Move -> [Node InternalNode Existential] -> Node InternalNode Universal
    E       :: Int -> Move -> [Node InternalNode Universal] -> Node InternalNode Existential
    SU      :: Int -> Move -> [Node InternalNode Existential] -> Node RootNode Universal
    SE      :: Int -> Move -> [Node InternalNode Universal] -> Node RootNode Existential

data SNode where
    SNode   :: Node t p -> SNode

class SNodeC (t :: NodeType) (p :: Player) where
    toNode      :: SNode -> Node t p

    viaSNode    :: (SNode -> SNode) -> Node t p -> Node t p
    viaSNode f n = toNode $ f (SNode n)

    mapNodes    :: (SNode -> SNode) -> [Node t p] -> [Node t p]
    mapNodes f = map (viaSNode f)

instance SNodeC InternalNode Universal where
    toNode (SNode u@(U _ _ _ _))    = u
    toNode _                        = error "Conversion to U Node failed"

instance SNodeC RootNode Universal where
    toNode (SNode u@(SU _ _ _))     = u
    toNode _                        = error "Conversion to SU Node failed"

instance SNodeC InternalNode Existential where
    toNode (SNode e@(E _ _ _))      = e
    toNode _                        = error "Conversion to E Node failed"

instance SNodeC RootNode Existential where
    toNode (SNode e@(SE _ _ _))     = e
    toNode _                        = error "Conversion to SE Node failed"

children :: SNode -> [SNode]
children (SNode (U _ _ _ cs)) = map SNode cs
children (SNode (E _ _ cs))   = map SNode cs
children (SNode (SU _ _ cs))  = map SNode cs
children (SNode (SE _ _ cs))  = map SNode cs

setChildren :: SNode -> [SNode] -> SNode
setChildren (SNode (U c m s _)) cs    = SNode (U c m s (map toNode cs))
setChildren (SNode (E c m _)) cs      = SNode (E c m (map toNode cs))
setChildren (SNode (SU c s _)) cs     = SNode (SU c s (map toNode cs))
setChildren (SNode (SE c s _)) cs     = SNode (SE c s (map toNode cs))

snodeMove :: SNode -> Move
snodeMove (SNode (U _ m _ _))     = m
snodeMove (SNode (E _ m _))       = m
snodeMove (SNode (SE _ s _))      = s
snodeMove (SNode (SU _ s _))      = s

setMove :: Move -> SNode -> SNode
setMove m (SNode (U c _ s n'))    = SNode (U c m s n')
setMove m (SNode (E c _ n'))      = SNode (E c m n')
setMove s (SNode (SU c _ n'))     = SNode (SU c s n')
setMove s (SNode (SE c _ n'))     = SNode (SE c s n')

snodeState :: SNode -> Move
snodeState (SNode (U _ _ s _))    = s
snodeState (SNode (E _ _ _))      = Nothing
snodeState (SNode (SU _ s _))     = s
snodeState (SNode (SE _ s _))     = s

copy :: SNode -> Int
copy (SNode (U c _ _ _))    = c
copy (SNode (E c _ _))      = c
copy (SNode (SU c _ _))     = c
copy (SNode (SE c _ _))     = c

setCopy :: Int -> SNode -> SNode 
setCopy c (SNode (U _ m s n))    = SNode (U c m s n)
setCopy c (SNode (E _ m n))      = SNode (E c m n)
setCopy c (SNode (SU _ s n))     = SNode (SU c s n)
setCopy c (SNode (SE _ s n))     = SNode (SE c s n)

data GameTree where
    ETree   :: {
          baseRank      :: Int
        , maxCopy       :: Int
        , crumb         :: [Int]
        , eroot         :: Node RootNode Universal
    } -> GameTree

    UTree   :: {
          baseRank      :: Int
        , maxCopy       :: Int
        , crumb         :: [Int]
        , uroot         :: Node RootNode Existential
    } -> GameTree

setCrumb :: GameTree -> [Int] -> GameTree
setCrumb t c = t { crumb = c }

root :: GameTree -> SNode
root ETree{..}  = SNode eroot
root UTree{..}  = SNode uroot

setRoot :: GameTree -> (SNode -> SNode) -> GameTree
setRoot t@(UTree{..}) f    = t { uroot = (viaSNode f uroot) }
setRoot t@(ETree{..}) f    = t { eroot = (viaSNode f eroot) }

-- |Construct a new game tree for player and rank specified
gtNew :: Player -> Int -> GameTree
gtNew Existential r = ETree { baseRank = r, maxCopy = 0, crumb = [], eroot = (SU 0 Nothing []) }
gtNew Universal r   = UTree { baseRank = r, maxCopy = 0, crumb = [], uroot = (SE 0 Nothing []) }

-- |Calculates rank of a node (based on base rank)
-- TODO: Needs to be fixed for swapping player order
gtRank :: GameTree -> Int
gtRank t    = (baseRank t) - (length (crumb t) `quot` 2)

-- |Returns the root node of the tree
gtBaseRank :: GameTree -> Int
gtBaseRank = baseRank

-- |Returns the first player of the tree (i.e. ETree or UTree)
gtFirstPlayer :: GameTree -> Player
gtFirstPlayer (ETree{}) = Existential
gtFirstPlayer (UTree{}) = Universal

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
playerNodeMoves Existential [] (SNode (E _ m _))        = [m]
playerNodeMoves Existential (c:cs) (SNode (E _ m ns))   = m : playerNodeMoves Existential cs (SNode (ns !! c))
playerNodeMoves Universal [] (SNode (U _ m _ _))        = [m]
playerNodeMoves Universal (c:cs) (SNode (U _ m _ ns))   = m : playerNodeMoves Universal cs (SNode (ns !! c))
playerNodeMoves p [] _                                  = []
playerNodeMoves p (c:cs) n                              = playerNodeMoves p cs (children n !! c)

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

gtCopyId :: GameTree -> Int
gtCopyId = copy . followGTCrumb

gtCopies :: GameTree -> [Int]
gtCopies gt = pc ++ replicate (((baseRank gt) * 2) - (length pc)) (last pc)
    where
        pc                  = pathCopies (root gt) (crumb gt)
        pathCopies n []     = [copy n]
        pathCopies n (c:cs) = copy n : pathCopies (children n !! c) cs

gtParent :: GameTree -> GameTree
gtParent gt = setCrumb gt (init (crumb gt))

gtPrevState :: GameTree -> Move
gtPrevState gt = snodeState $ followCrumb (root gt) (prevStateNode gt (crumb gt))

gtPrevStateGT :: GameTree -> GameTree
gtPrevStateGT gt = setCrumb gt (prevStateNode gt (crumb gt))

prevStateNode :: GameTree -> [Int] -> [Int]
prevStateNode gt cr = case followCrumb (root gt) cr of
    (SNode (E _ _ _))     -> init cr
    (SNode (U _ _ _ _))   -> init (init cr)

-- |Creates a new tree with the current node as its base
gtRebase :: GameTree -> GameTree
gtRebase gt = ETree { baseRank = newrank, maxCopy = 0, crumb =  [], eroot = (SU 0 Nothing [(toNode newroot)]) }
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
gtMovePairs :: GameTree -> [(Move, Move, Maybe GameTree)]
gtMovePairs gt = case (zip (children n) [0..]) of
    []  -> [(snodeMove n, Nothing, Nothing)]
    cs  -> map (\(x, y) -> (snodeMove n, snodeMove x, Just (setCrumb gt (crumb gt ++ [y])))) cs
    where
        n = followGTCrumb gt

stateFromPair :: SNode -> SNode -> Move
stateFromPair (SNode (E _ _ _)) (SNode (U _ _ s _)) = s
stateFromPair (SNode (U _ _ s _)) (SNode (E _ _ _)) = s

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
        makePN (c:cs) (SNode (E i m ns))      = SNode (E i m [viaSNode (makePN cs) (ns !! c)])
        makePN (c:cs) (SNode (U i m s ns))    = SNode (U i m s [viaSNode (makePN cs) (ns !! c)])
        makePN (c:cs) (SNode (SE i s ns))     = SNode (SE i s [viaSNode (makePN cs) (ns !! c)])
        makePN (c:cs) (SNode (SU i s ns))     = SNode (SU i s [viaSNode (makePN cs) (ns !! c)])

-- |Fix moves for one player in a path tree only
fixPlayerMoves :: Player -> GameTree -> [([Assignment], [Assignment])] -> GameTree
fixPlayerMoves p gt as = setRoot gt (fpm p as)
    where
        fpm Existential ((m,s):as) (SNode (E c _ ns))   = SNode (E c (Just m) (mapNodes (fpm p ((m,s):as)) ns))
        fpm Existential ((_,s):as) (SNode (U c m _ ns)) = SNode (U c m (Just s) (mapNodes (fpm p as) ns))

        fpm Universal ((m,s):as) (SNode (U c _ _ ns))   = SNode (U c (Just m) (Just s) (mapNodes (fpm p as) ns))
        fpm p as n                                      = setChildren n (map (fpm p as) (children n))

fixInitState :: [Assignment] -> GameTree -> GameTree
fixInitState s gt = setRoot gt fsi
    where
        fsi (SNode (SU c _ ns))   = SNode (SU c (Just s) ns)
        fsi (SNode (SE c _ ns))   = SNode (SE c (Just s) ns)

-- |Project moves from one game tree onto another
projectMoves :: GameTree -> GameTree -> Maybe GameTree
projectMoves t1@(ETree{}) t2@(ETree{})  = do
    p <- projectNodes (root t1) (root t2)
    return $ t1 { eroot = (toNode p) }
projectMoves t1@(UTree{}) t2@(UTree{})  = do
    p <- projectNodes (root t1) (root t2) 
    return $ t2 { uroot = (toNode p) }
projectMoves _ _                            = Nothing

projectNodes :: SNode -> SNode -> Maybe SNode
projectNodes (SNode (E c m ns))   (SNode (E cp mp ps))
    | isNothing m   = maybeProject (SNode (E c mp [])) ns ps
    | m == mp       = maybeProject (SNode (E c m [])) ns ps
    | otherwise     = D.trace (show m ++ "\n" ++ show mp) $ Nothing
projectNodes (SNode (U c m s ns)) (SNode (U cp mp sp ps))
    | isNothing m   = maybeProject (SNode (U c mp sp [])) ns ps
    | m == mp       = maybeProject (SNode (U c m sp [])) ns ps
    | otherwise     = D.trace "2" $ Nothing
projectNodes (SNode (SE c s ns))  (SNode (SE cp sp ps))
    | isNothing s   = maybeProject (SNode (SE c sp [])) ns ps
    | s == sp       = maybeProject (SNode (SE c s [])) ns ps
    | otherwise     = D.trace "3" $ Nothing
projectNodes (SNode (SU c s ns))  (SNode (SU cp sp ps))
    | isNothing s   = maybeProject (SNode (SU c sp [])) ns ps
    | s == sp       = maybeProject (SNode (SU c s [])) ns ps
    | otherwise     = D.trace "4" $ Nothing

maybeProject :: SNode -> [Node t p] -> [Node t p] -> Maybe SNode
maybeProject s ns ps = do
    ns' <- zipWithM projectNodes (map SNode ns) (map SNode ps)
    return $ setChildren s ns'

mergeTrees :: GameTree -> GameTree -> GameTree
mergeTrees t1 t2 = setRoot (setCrumb t1 []) (\_ -> r)
    where
        r = mergeNodes (root t1) (Just (root t2))

mergeNodes :: SNode -> Maybe SNode -> SNode
mergeNodes x (Just y)    = setChildren x (map (uncurry mergeNodes) (zipChildren (children x) (children y)))
mergeNodes n Nothing     = n

zipChildren :: [SNode] -> [SNode] -> [(SNode, Maybe SNode)]
zipChildren xs []           = map (\x -> (x, Nothing)) xs
zipChildren [] ys           = map (\y -> (y, Nothing)) ys
zipChildren (x:xs) (y:ys)   = if snodeMove x == snodeMove y
    then (x, Just y) : zipChildren xs ys
    else (x, Nothing) : zipChildren xs (y:ys)

appendChild :: GameTree -> GameTree
appendChild gt = gt' { maxCopy = c }
    where
        (c, r)  = appendNodeAt (maxCopy gt) (crumb gt) (root gt)
        gt'     = setRoot gt (\x -> r)

appendNodeAt mc [] n       = appendNode mc Nothing Nothing n
appendNodeAt mc (c:cs) n   = (mc', setChildren n (update n' c ns))
    where
        ns          = children n
        (mc', n')   = appendNodeAt mc cs (ns !! c)

appendNode :: Int -> Move -> Move -> SNode -> (Int, SNode)
appendNode mc m' s' n = (mc', app n)
    where
        app (SNode (E c m ns))      = SNode (E c m (ns ++ [U c' m' s' []]))
        app (SNode (U c m s ns))    = SNode (U c m s (ns ++ [E c' m' []]))
        app (SNode (SE c s ns))     = SNode (SE c s (ns ++ [U c' m' s' []]))
        app (SNode (SU c s ns))     = SNode (SU c s (ns ++ [E c' m' []]))
        (mc', c')                   = appendCopy mc (copy n) (children n)

append2Nodes :: Int -> Move -> Move -> SNode -> (Int, SNode)
append2Nodes mc m' s' n = (mc', app n)
    where
        app (SNode (E c m ns))      = SNode (E c m (ns ++ [U c' m' s' [E c' Nothing []]]))
        app (SNode (U c m s ns))    = SNode (U c m s (ns ++ [E c' m' [U c' Nothing Nothing []]]))
        app (SNode (SE c s ns))     = SNode (SE c s (ns ++ [U c' m' s' [E c' Nothing []]]))
        app (SNode (SU c s ns))     = SNode (SU c s (ns ++ [E c' m' [U c' Nothing Nothing []]]))
        (mc', c')                   = appendCopy mc (copy n) (children n)

appendCopy mc c [] = (mc, c)
appendCopy mc _ ns = (mc+1, mc+1)

-- |Appends the first move in the list that is not already in the tree
appendNextMove :: GameTree -> GameTree -> GameTree
appendNextMove gt cex = gt' { maxCopy = mc }
    where
        (mc, r) = appendMove (baseRank gt * 2) (maxCopy gt) (root cex) (root gt)
        gt'     = setRoot gt (\x -> r)

appendMove :: Int -> Int -> SNode -> SNode -> (Int, SNode)
appendMove r mc cex n
    | null cs   = (mc, n)
    | null ns   = addNew mc (snodeMove (head cs)) (snodeState (head cs)) n
    | otherwise = foldl addMove (foldl (recur r) (mc, n) ms) nms
    where
        cs                  = children cex
        ns                  = children n
        moveEq x y          = snodeMove x == snodeMove y || snodeMove y == Nothing
        (ms, nms)           = matchIndices moveEq (children cex) (children n)
        addNew              = if r <= 1 then appendNode else append2Nodes
        addMove (c, x) y    = addNew c (snodeMove y) (snodeState y) x

recur :: Int -> (Int, SNode) -> (SNode, Int) -> (Int, SNode)
recur r (mc, n) (m, i)    = (mc', setChildren n (update n' i ns))
    where
        ns          = children n
        (mc', n')   = appendMove (r-1) mc m (ns !! i)

matchIndices :: (a -> a -> Bool) -> [a] -> [a] -> ([(a, Int)], [a])
matchIndices _ [] _         = ([], [])
matchIndices f (x:xs) ys    = if isJust m 
    then mapFst (\ps -> ps ++ [(x, fromJust m)]) (matchIndices f xs ys)
    else mapSnd (\ns -> ns ++ [x]) (matchIndices f xs ys)
    where
        m                   = match 0 x ys
        match i a []        = Nothing
        match i a (b:bs)    = if f a b then Just i else match (i+1) a bs

printTree :: CompiledSpec -> GameTree -> String
printTree spec gt = "---\n" ++ printNode spec 0 (root gt) ++ "---"

printNode :: CompiledSpec -> Int -> SNode -> String
printNode spec t (SNode (E c m cs))     = tab t ++ "E " ++ show c ++ " " ++ printMove spec m ++ "\n" ++ concatMap (printNode spec (t+1)) (map SNode cs)
printNode spec t (SNode (U c m s cs))   = tab t ++ "U " ++ show c ++ " " ++ printMove spec m ++ " | " ++ printMove spec s ++ "\n" ++ concatMap (printNode spec (t+1)) (map SNode cs)
printNode spec t (SNode (SE c s cs))    = tab t ++ "SE " ++ show c ++ " " ++ printMove spec s ++ "\n" ++ concatMap (printNode spec (t+1)) (map SNode cs)
printNode spec t (SNode (SU c s cs))    = tab t ++ "SU " ++ show c ++ " " ++ printMove spec s ++ "\n" ++ concatMap (printNode spec (t+1)) (map SNode cs)

tab ind = concat (replicate ind "| ") ++ "|-"

printMove :: CompiledSpec -> Move -> String
printMove spec Nothing   = "Nothing"
printMove spec (Just as) = interMap ", " (printVar spec) vs
    where
        vs = groupBy f as
        f (Assignment _ x) (Assignment _ y) = varname x == varname y

printVar :: CompiledSpec -> [Assignment] -> String
printVar spec as = vname ++ show vrank ++ " = " ++ valsToEnums vi vals
    where
        vname       = let (Assignment _ v) = (head as) in varname v
        vrank       = let (Assignment _ v) = (head as) in rank v
        (Just vi)   = find (\v -> name v == vname) (vinfo spec)
        vals        = signsToVals 1 [0] (map f [0..(sz vi)-1])
        f b         = fmap sign (find (\(Assignment s v) -> bit v == b) as)

sign (Assignment s _) = s

signsToVals v vs []                   = vs
signsToVals v vs (Nothing: bs)        = signsToVals (v*2) (vs ++ map (+ v) vs) bs
signsToVals v vs ((Just Pos): bs)     = signsToVals (v*2) (map (+ v) vs) bs
signsToVals v vs ((Just Neg): bs)     = signsToVals (v*2) vs bs

valsToEnums VarInfo {enum = Nothing} (v:[])     = show v
valsToEnums VarInfo {enum = Nothing} vs         = show vs
valsToEnums VarInfo {enum = Just eMap} (v:[])   = fromMaybe (show v) (lookup v (map swap eMap))
valsToEnums VarInfo {enum = Just eMap} vs       = "[" ++ interMap ", " (\v -> fromMaybe (show v) (lookup v (map swap eMap))) vs ++ "]"

validTree :: GameTree -> Bool
validTree gt = any ((/= Nothing) . snodeMove) $ map followGTCrumb (gtLeaves gt)
