{-# LANGUAGE GADTs, KindSignatures, DataKinds, MultiParamTypeClasses, RecordWildCards, ViewPatterns #-}
module Synthesise.GameTree (
      GameTree
    , Player(..)
    , Move(..)
    , printMove
    , opponent

    -- Queries on GameTrees
    , gtRank
    , gtAtBottom
    , gtRoot
    , gtBaseRank
    , gtMaxCopy
    , gtFirstPlayer
    , gtCrumb
    , gtMoves
    , gtMove
    , gtState
    , gtCopyId
    , gtNodeId
    , gtParent
    , gtPathMoves
    , gtMaxDepth
    , gtChildMoves
    , gtChildren
    , gtSetChildren
    , gtMovePairs
    , gtUnsetNodes
    , gtPrevState
    , gtPrevStateGT
    , gtRebase
    , printTree

    -- Modifiers
    , gtNew
    , gtLeaves
    , makePathTree
    , gtCached
    , gtSetMove
    , gtSetState
    , gtSetInit
    , gtSetExprId
    , projectMoves
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
    U :: {
          uCopy         :: Int
        , uNodeId       :: Int
        , uMove         :: Move
        , uState        :: Move
        , uChanged      :: Bool
        , uExprId       :: Maybe Int
        , uChildren     :: [Node InternalNode Existential]
    } -> Node InternalNode Universal

    E :: {
          eCopy         :: Int
        , eNodeId       :: Int
        , eMove         :: Move
        , eChanged      :: Bool
        , eExprId       :: Maybe Int
        , eChildren     :: [Node InternalNode Universal]
    } -> Node InternalNode Existential

    SU :: {
          suCopy        :: Int
        , suNodeId      :: Int
        , suState       :: Move
        , suChanged     :: Bool
        , suExprId      :: Maybe Int
        , suChildren    :: [Node InternalNode Existential]
    } -> Node RootNode Universal

    SE :: {
          seCopy        :: Int
        , seNodeId      :: Int
        , seState       :: Move
        , seChanged     :: Bool
        , seExprId      :: Maybe Int
        , seChildren    :: [Node InternalNode Universal]
    } -> Node RootNode Existential

data SNode where
    SNode   :: Node t p -> SNode

class SNodeC (t :: NodeType) (p :: Player) where
    toNode      :: SNode -> Node t p

    viaSNode    :: (SNode -> SNode) -> Node t p -> Node t p
    viaSNode f n = toNode $ f (SNode n)

    mapNodes    :: (SNode -> SNode) -> [Node t p] -> [Node t p]
    mapNodes f = map (viaSNode f)

instance SNodeC InternalNode Universal where
    toNode (SNode u@(U{}))  = u
    toNode _                = error "Conversion to U Node failed"

instance SNodeC RootNode Universal where
    toNode (SNode u@(SU{})) = u
    toNode _                = error "Conversion to SU Node failed"

instance SNodeC InternalNode Existential where
    toNode (SNode e@(E{}))  = e
    toNode _                = error "Conversion to E Node failed"

instance SNodeC RootNode Existential where
    toNode (SNode e@(SE{})) = e
    toNode _                = error "Conversion to SE Node failed"

newNode :: SNode -> Int -> Int -> Move -> Move -> SNode
newNode (SNode E{}) id c m s    = SNode $ U { uCopy = c, uNodeId = id, uMove = m, uChanged = False, uExprId = Nothing, uState = s, uChildren = [] }
newNode (SNode U{}) id c m s    = SNode $ E { eCopy = c, eNodeId = id, eMove = m, eChanged = False, eExprId = Nothing, eChildren = [] }
newNode (SNode SE{}) id c m s   = SNode $ U { uCopy = c, uNodeId = id, uMove = m, uChanged = False, uExprId = Nothing, uState = s, uChildren = [] }
newNode (SNode SU{}) id c m s   = SNode $ E { eCopy = c, eNodeId = id, eMove = m, eChanged = False, eExprId = Nothing, eChildren = [] }

children :: SNode -> [SNode]
children (SNode n@U{})  = map SNode (uChildren n)
children (SNode n@E{})  = map SNode (eChildren n)
children (SNode n@SU{}) = map SNode (suChildren n)
children (SNode n@SE{}) = map SNode (seChildren n)

setChildren :: SNode -> [SNode] -> SNode
setChildren (SNode n@U{}) cs    = SNode (n { uChildren = map toNode cs })
setChildren (SNode n@E{}) cs    = SNode (n { eChildren = map toNode cs })  
setChildren (SNode n@SU{}) cs   = SNode (n { suChildren = map toNode cs })  
setChildren (SNode n@SE{}) cs   = SNode (n { seChildren = map toNode cs })  

snodeMove :: SNode -> Move
snodeMove (SNode n@U{})     = uMove n
snodeMove (SNode n@E{})     = eMove n
snodeMove (SNode n@SU{})    = suState n
snodeMove (SNode n@SE{})    = seState n

isChanged :: SNode -> Bool
isChanged (SNode n@U{})     = uChanged n
isChanged (SNode n@E{})     = eChanged n
isChanged (SNode n@SU{})    = suChanged n
isChanged (SNode n@SE{})    = seChanged n

setChanged :: SNode -> Bool -> SNode
setChanged (SNode n@U{}) c  = SNode (n { uChanged = c })
setChanged (SNode n@E{}) c  = SNode (n { eChanged = c })
setChanged (SNode n@SU{}) c = SNode (n { suChanged = c })
setChanged (SNode n@SE{}) c = SNode (n { seChanged = c })

setMove :: Move -> SNode -> SNode
setMove m (SNode n@U{..})   = SNode (n { uMove = m, uChanged = uChanged || m /= uMove })
setMove m (SNode n@E{..})   = SNode (n { eMove = m, eChanged = eChanged || m /= eMove })
setMove s (SNode n@SU{..})  = SNode (n { suState = s, suChanged = suChanged || s /= suState })
setMove s (SNode n@SE{..})  = SNode (n { seState = s, seChanged = seChanged || s /= seState })

snodeState :: SNode -> Move
snodeState (SNode n@U{})     = uState n
snodeState (SNode n@E{})     = Nothing
snodeState (SNode n@SU{})    = suState n
snodeState (SNode n@SE{})    = seState n

setState :: Move -> SNode -> SNode
setState s (SNode n@U{})     = SNode (n { uState = s })
setState _ (SNode n@E{})     = error "Trying to set state of Existential node"
setState s (SNode n@SU{})    = SNode (n { suState = s })
setState s (SNode n@SE{})    = SNode (n { seState = s })

setStateIfU :: Move -> SNode -> SNode
setStateIfU m (SNode n@U{}) = SNode (n { uState = m })
setStateIfU _ n             = n

getStateIfU :: SNode -> Maybe Move
getStateIfU (SNode n@U{})   = Just (uState n)
getStateIfU _               = Nothing

copy :: SNode -> Int
copy (SNode n@U{})     = uCopy n
copy (SNode n@E{})     = eCopy n
copy (SNode n@SU{})    = suCopy n
copy (SNode n@SE{})    = seCopy n

setCopy :: Int -> SNode -> SNode 
setCopy c (SNode n@U{})     = SNode (n { uCopy = c })
setCopy c (SNode n@E{})     = SNode (n { eCopy = c })
setCopy c (SNode n@SU{})    = SNode (n { suCopy = c })
setCopy c (SNode n@SE{})    = SNode (n { seCopy = c })

nodeId :: SNode -> Int
nodeId (SNode n@U{})    = uNodeId n
nodeId (SNode n@E{})    = eNodeId n
nodeId (SNode n@SU{})   = suNodeId n
nodeId (SNode n@SE{})   = seNodeId n

data GameTree where
    ETree   :: {
          baseRank      :: Int
        , maxCopy       :: Int
        , maxId         :: Int
        , crumb         :: [Int]
        , eroot         :: Node RootNode Universal
    } -> GameTree

    UTree   :: {
          baseRank      :: Int
        , maxCopy       :: Int
        , maxId         :: Int
        , crumb         :: [Int]
        , uroot         :: Node RootNode Existential
    } -> GameTree

setCrumb :: GameTree -> [Int] -> GameTree
setCrumb t c = t { crumb = c }

root :: GameTree -> SNode
root ETree{..}  = SNode eroot
root UTree{..}  = SNode uroot

setRoot :: GameTree -> SNode -> GameTree
setRoot t@(UTree{..}) r     = t { uroot = toNode r }
setRoot t@(ETree{..}) r     = t { eroot = toNode r }

updateRoot :: GameTree -> (SNode -> SNode) -> GameTree
updateRoot t@(UTree{..}) f  = t { uroot = (viaSNode f uroot) }
updateRoot t@(ETree{..}) f  = t { eroot = (viaSNode f eroot) }

-- |Construct a new game tree for player and rank specified
gtNew :: Player -> Int -> GameTree
gtNew Existential r = ETree {
      baseRank  = r
    , maxCopy   = 0
    , maxId     = 1
    , crumb     = []
    , eroot     = SU { suCopy = 0, suNodeId = 0, suState = Nothing, suChanged = False, suExprId = Nothing, suChildren = [] } }

gtNew Universal r   = UTree { 
      baseRank  = r
    , maxCopy   = 0
    , maxId     = 1
    , crumb     = []
    , uroot     = SE { seCopy = 0, seNodeId = 0, seState = Nothing, seChanged = False, seExprId = Nothing, seChildren = [] } }

-- |Calculates rank of a node (based on base rank)
gtRank :: GameTree -> Int
gtRank t@(crumb -> [])  = baseRank t
gtRank t                = baseRank t - ((length (crumb t) - 1) `quot` 2)

gtAtBottom :: GameTree -> Bool
gtAtBottom t@(ETree{})  = gtRank t == 1 && isUNode (followGTCrumb t)
gtAtBottom t@(UTree{})  = gtRank t == 1 && isENode (followGTCrumb t)

isUNode (SNode (U{}))   = True
isUNode _               = False

isENode (SNode (E{}))   = True
isENode _               = False

-- |Returns the root node of the tree
gtBaseRank :: GameTree -> Int
gtBaseRank = baseRank

gtMaxCopy :: GameTree -> Int
gtMaxCopy = maxCopy

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

gtNodeId :: GameTree -> Int
gtNodeId = nodeId . followGTCrumb

gtParent :: GameTree -> GameTree
gtParent gt = setCrumb gt (init (crumb gt))

gtPrevState :: GameTree -> Move
gtPrevState gt = snodeState $ followCrumb (root gt) (prevStateNode gt (crumb gt))

gtPrevStateGT :: GameTree -> GameTree
gtPrevStateGT gt = setCrumb gt (prevStateNode gt (crumb gt))

prevStateNode :: GameTree -> [Int] -> [Int]
prevStateNode gt cr = case followCrumb (root gt) cr of
    (SNode (E{}))   -> init cr
    (SNode (U{}))   -> init (init cr)

-- |Creates a new tree with the current node as its base
gtRebase :: GameTree -> GameTree
gtRebase gt = updateRoot (gtNew Existential newrank) (`setChildren` [newroot])
    where
        newcrumb    = alignCrumb (crumb gt)
        newroot     = followCrumb (root gt) newcrumb
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

updateGTCrumb :: GameTree -> (SNode -> SNode) -> GameTree
updateGTCrumb gt f = updateRoot gt (updateCrumb f (crumb gt))

updateCrumb :: (SNode -> SNode) -> [Int] -> SNode -> SNode
updateCrumb f [] n      = f n
updateCrumb f (c:cs) n  = setChildren n (adjust (updateCrumb f cs) c (children n))

-- |Gets all outgoing moves of a node
gtChildMoves :: GameTree -> [Move]
gtChildMoves gt = map snodeMove (children (followGTCrumb gt))

gtChildren :: GameTree -> [GameTree]
gtChildren gt = zipWith f (children (followGTCrumb gt)) [0..]
    where
        f n i = setCrumb gt (crumb gt ++ [i])

gtSetChildren :: GameTree -> [GameTree] -> GameTree
gtSetChildren gt cs = updateGTCrumb gt f
    where
        f n = setChildren n (map followGTCrumb cs)

-- |Groups moves by rank
gtMovePairs :: GameTree -> [(Move, Move, Maybe GameTree)]
gtMovePairs gt = case (zip (children n) [0..]) of
    []  -> [(snodeMove n, Nothing, Nothing)]
    cs  -> map (\(x, y) -> (snodeMove n, snodeMove x, Just (setCrumb gt (crumb gt ++ [y])))) cs
    where
        n = followGTCrumb gt

stateFromPair :: SNode -> SNode -> Move
stateFromPair (SNode (E{})) (SNode n@(U{})) = uState n
stateFromPair (SNode n@(U{})) (SNode (E{})) = uState n

-- |Finds the first Nothing move
gtUnsetNodes :: GameTree -> [GameTree]
gtUnsetNodes gt = map (setCrumb gt) $ filter (not . null) $ map (firstUnsetNode (root gt) 0) (getLeaves (root gt))

firstUnsetNode r cc cr
    | cc == length cr + 1                                   = []
    | isNothing (snodeMove (followCrumb r (take cc cr)))    = take cc cr
    | otherwise                                             = firstUnsetNode r (cc + 1) cr

-- |Filters moves not in the crumb out
makePathTree :: GameTree -> GameTree
makePathTree gt = setCrumb (updateRoot gt (makePN (crumb gt))) (replicate (length (crumb gt)) 0)
    where
        makePN [] n     = n
        makePN (c:cs) n = setChildren n [makePN cs (children n !! c)]

gtCached :: GameTree -> GameTree
gtCached gt = setRoot gt (mapChildren (root gt))
    where
        mapChildren n = setChildren (setChanged n False) (map mapChildren (children n))

gtSetMove :: GameTree -> [Assignment] -> GameTree
gtSetMove gt as = updateGTCrumb gt (setMove (Just as))

gtSetState :: GameTree -> [Assignment] -> GameTree
gtSetState gt as = updateGTCrumb gt (setState (Just as))

gtSetInit :: [Assignment] -> GameTree -> GameTree
gtSetInit s gt = updateRoot gt fsi
    where
        fsi (SNode n@(SU{}))    = SNode (n { suState = Just s })
        fsi (SNode n@(SE{}))    = SNode (n { seState = Just s })

gtSetExprId :: GameTree -> Int -> GameTree
gtSetExprId gt e = gt

-- |Project moves from one game tree onto another
projectMoves :: GameTree -> GameTree -> Maybe GameTree
projectMoves t1 t2 = (liftM (setRoot t1)) (projectNodes (root t1) (root t2))

projectNodes :: SNode -> SNode -> Maybe SNode
projectNodes n p
    | nodeId n == nodeId p = do
        cs <- zipWithM projectNodes (children n) (children p)
        return $ setStateIfU (snodeState p) (setMove (snodeMove p) (setChildren n cs))
    | otherwise = D.trace (show (snodeMove n) ++ show (snodeMove p)) $ Nothing

appendChild :: GameTree -> GameTree
appendChild gt = gt' { maxCopy = c, maxId = n }
    where
        (c, n, r)   = appendNodeAt (maxCopy gt) (maxId gt) (crumb gt) (root gt)
        gt'         = setRoot gt r

appendNodeAt mc mn [] n       = appendNode mc mn Nothing Nothing n
appendNodeAt mc mn (c:cs) n   = (mc', mn', setChildren n (update n' c ns))
    where
        ns              = children n
        (mc', mn', n')  = appendNodeAt mc mn cs (ns !! c)

appendNode :: Int -> Int -> Move -> Move -> SNode -> (Int, Int, SNode)
appendNode mc mn m' s' n = (mc', mn+1, setChildren n (children n ++ [newNode n mn c' m' s']))
    where
        (mc', c')           = appendCopy mc (copy n) (children n)

append2Nodes :: Int -> Int -> Move -> Move -> SNode -> (Int, Int, SNode)
append2Nodes mc mn m' s' n = (mc', mn+2, setChildren n (children n ++ [n'']))
    where
        n'          = newNode n mn c' m' s'
        n''         = setChildren n' ([newNode n' (mn + 1) c' Nothing Nothing])
        (mc', c')   = appendCopy mc (copy n) (children n)

appendCopy mc c [] = (mc, c)
appendCopy mc _ ns = (mc+1, mc+1)

-- |Appends the first move in the list that is not already in the tree
appendNextMove :: GameTree -> GameTree -> GameTree
appendNextMove gt cex = gt' { maxCopy = mc, maxId = mn }
    where
        (mc, mn, r) = appendMove (baseRank gt * 2) (maxCopy gt) (maxId gt) (root cex) (root gt)
        gt'         = setRoot gt r

appendMove :: Int -> Int -> Int -> SNode -> SNode -> (Int, Int, SNode)
appendMove r mc mn cex n
    | null cs   = (mc, mn, n)
    | null ns   = addNew mc mn (snodeMove (head cs)) (snodeState (head cs)) n
    | otherwise = foldl addMove (foldl (recur r) (mc, mn, n) ms) nms
    where
        cs                  = children cex
        ns                  = children n
        moveEq x y          = equalModCopy (snodeMove x) (snodeMove y) || snodeMove y == Nothing
        (ms, nms)           = matchIndices moveEq (children cex) (children n)
        addNew              = if r <= 1 then appendNode else append2Nodes
        addMove (c, i, x) y = addNew c i (snodeMove y) (snodeState y) x

equalModCopy (Just xs) (Just ys)    = all (uncurry aEqualModCopy) (zip xs ys)
    where
        aEqualModCopy (Assignment sx x) (Assignment sy y) = sx == sy && x {ecopy = 0} == y {ecopy = 0}
equalModCopy _ _                    = False

recur :: Int -> (Int, Int, SNode) -> (SNode, Int) -> (Int, Int, SNode)
recur r (mc, mn, n) (m, i)    = (mc', mn', setChildren n (update n' i ns))
    where
        ns              = children n
        (mc', mn', n')  = appendMove (r-1) mc mn m (ns !! i)

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
printTree spec gt = "---\n" ++ printNode spec 0 (Just (crumb gt)) (root gt) ++ "---"

printNode :: CompiledSpec -> Int -> Maybe [Int] -> SNode -> String
printNode spec t cs n = tab t 
    ++ (if maybe False null cs then "*" else "")
    ++ printNodeType n 
---    ++ show (nodeId n) ++ " "
    ++ show (copy n) ++ " "
---    ++ show (isChanged n) ++ " "
    ++ printMove spec (snodeMove n) 
    ++ maybe "" ((" | " ++) . printMove spec) (getStateIfU n) 
    ++ "\n" ++ concatMap (printNode spec (t+1) (nextC cs)) (children n)
    where
        nextC Nothing       = Nothing
        nextC (Just [])     = Nothing
        nextC (Just (c:cs)) = Just cs
        

printNodeType :: SNode -> String
printNodeType (SNode n@(E{}))    = "E "
printNodeType (SNode n@(U{}))    = "U "
printNodeType (SNode n@(SE{}))   = "SE "
printNodeType (SNode n@(SU{}))   = "SU "

tab ind = concat (replicate ind "| ") ++ "|-"

printMove :: CompiledSpec -> Move -> String
printMove spec Nothing   = "Nothing"
printMove spec (Just as) = interMap ", " (printVar spec) vs
    where
        vs = groupBy f as
        f (Assignment _ x) (Assignment _ y) = varname x == varname y

printVar :: CompiledSpec -> [Assignment] -> String
printVar spec as = vname ++ show vrank ++ {- "_" ++ show vcopy ++ -} " = " ++ valsToEnums vi vals
    where
        vname       = let (Assignment _ v) = (head as) in varname v
        vrank       = let (Assignment _ v) = (head as) in rank v
        vcopy       = let (Assignment _ v) = (head as) in ecopy v
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
