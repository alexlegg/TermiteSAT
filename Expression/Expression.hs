{-# LANGUAGE RecordWildCards #-}
module Expression.Expression (
      ExpressionT(..)
    , ExprType(..)
    , ExprVar(..)
    , Expression(..)
    , Section(..)
    , Sign(..)
    , Var(..)

    , flipSign
    , emptyManager
    , addExpression
    , getChildren
    , lookupExpression
    , getMaxIndex
    , traverseExpression
    , foldlExpression
    , foldrExpression
    , unrollExpression
    , setRank
    , conjunct
    , disjunct
    , equate
    , implicate
    , negation
    , equalsConstant
    , trueExpr
    , falseExpr
    , toDimacs
    , makeCopy
    , printExpression
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Bits (testBit)
import Data.Foldable (foldlM)
import Data.Maybe
import Utils.Utils
import Debug.Trace

type ExpressionT m a = StateT ExprManager (EitherT String m) a

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . left

data ExprType = ETrue
              | EFalse
              | EConjunct
              | EDisjunct
              | EEquals
              | ENot
              | ELit ExprVar
              | ECopy Int
    deriving (Show, Eq, Ord)

data ExprVar = ExprVar {
    varname     :: String,
    varsect     :: Section,
    bit         :: Int,
    varcopy     :: Int,
    rank        :: Int
    } deriving (Eq, Ord)

instance Show ExprVar where
    show v = let ExprVar{..} = v in varname ++ show rank ++ "[" ++ show bit ++ "](" ++ show varcopy ++ ")"

data Var = Var Sign Int deriving (Show, Eq, Ord)

var (Var _ v)   = v
sign (Var s _)  = s
lit (Var Pos v) = v
lit (Var Neg v) = -v

data Sign = Pos | Neg deriving (Show, Eq, Ord)

flipSign Pos = Neg
flipSign Neg = Pos

data Expression = Expression {
    index           :: Int,
    operation       :: ExprType,
    children        :: [Var]
}

instance Eq Expression where
    x == y      = operation x == operation y && children x == children y

instance Ord Expression where
    x <= y      = if operation x == operation y
                    then children x <= children y
                    else operation x <= operation y 

instance Show Expression where
    show e = let Expression{..} = e in
        show index ++ " = " ++
        case operation of
            ETrue       -> "T"
            EFalse      -> "F"
            EConjunct   -> "conj {" ++ intercalate ", " (map show children) ++ "}"
            EDisjunct   -> "disj {" ++ intercalate ", " (map show children) ++ "}"
            EEquals     -> "equal {" ++ intercalate ", " (map show children) ++ "}"
            ENot        -> "not {" ++ intercalate ", " (map show children) ++ "}"
            ELit v      -> show v

data ExprManager = ExprManager {
    maxIndex        :: Int,
    exprMap         :: Map.Map Int Expression,
    indexMap        :: Map.Map Expression Int,
    copyIndex       :: Int
} deriving (Eq)

instance Show ExprManager where
    show m = let ExprManager{..} = m in
        "maxIndex: " ++ show maxIndex ++
        Map.foldl (\a b -> a ++ "\n" ++ show b) "" exprMap

data Section = StateVar | ContVar | UContVar
    deriving (Show, Eq, Ord)

emptyManager = ExprManager { maxIndex = 3, exprMap = Map.empty, indexMap = Map.empty, copyIndex = 0 }

addExpression :: Monad m => ExprType -> [Var] -> ExpressionT m Expression
addExpression e c = do
    m@ExprManager{..} <- get
    let expr = Expression maxIndex e c
    case Map.lookup expr indexMap of
        Nothing -> do
            put m {
                maxIndex    = maxIndex+1,
                exprMap     = Map.insert maxIndex expr exprMap,
                indexMap    = Map.insert expr maxIndex indexMap}
            return expr
        Just i -> do
            return $ fromJust (Map.lookup i exprMap)

lookupExpression :: Monad m => Int -> ExpressionT m (Maybe Expression)
lookupExpression i = do
    ExprManager{..} <- get
    return $ Map.lookup i exprMap

getChildren :: Monad m => Expression -> ExpressionT m [Expression]
getChildren e = do
    es <- mapM (lookupExpression . var) (children e)
    return (catMaybes es)

getMaxIndex :: Monad m => ExpressionT m Int
getMaxIndex = do
    ExprManager{..} <- get
    return maxIndex

foldlExpression :: Monad m => (a -> Expression -> a) -> a -> Expression -> ExpressionT m a
foldlExpression f x e = do
    cs <- getChildren e
    foldlM (foldlExpression f) (f x e) cs

foldrExpression :: Monad m => (Expression -> a -> a) -> a -> Expression -> ExpressionT m a
foldrExpression f x e = do
    cs <- getChildren e
    foldlM (foldrExpression f) (f e x) cs

traverseExpression :: Monad m => (ExprType -> ExprType) -> Expression -> ExpressionT m Expression
traverseExpression f e = do
    let signs = map sign (children e)
    cs <- getChildren e
    cs' <- mapM (traverseExpression f) cs
    let cs'' = map (uncurry Var) (zip signs (map index cs'))
    addExpression (f (operation e)) cs''

setRank :: Monad m => Int -> Expression -> ExpressionT m Expression
setRank r = traverseExpression (setVarRank r)
    
setVarRank r (ELit v)   = ELit (v {rank = r})
setVarRank _ x          = x

unrollExpression :: Monad m => Expression -> ExpressionT m Expression
unrollExpression = traverseExpression shiftVar

shiftVar (ELit v)   = ELit (v {rank = rank v + 1})
shiftVar x          = x

liftExprType t e = if operation e == t then children e else [Var Pos (index e)]

-- |The 'conjunct' function takes a list of Expressions and produces one conjunction Expression
conjunct :: Monad m => [Expression] -> ExpressionT m Expression
conjunct es = do
    case length es of
        0 -> addExpression EFalse []
        1 -> return (head es)
        _ -> addExpression EConjunct (concatMap (liftExprType EConjunct) es)

-- |The 'disjunct' function takes a list of Expressions and produces one disjunction Expression
disjunct :: Monad m => [Expression] -> ExpressionT m Expression
disjunct es = do
    case length es of
        0 -> addExpression ETrue []
        1 -> return (head es)
        _ -> addExpression EDisjunct (concatMap (liftExprType EDisjunct) es)

makeSignsFromValue :: Int -> Int -> [Sign]
makeSignsFromValue v sz = map f [0..(sz-1)]
    where
        f b = if testBit v b then Pos else Neg

equalsConstant :: Monad m => [ExprVar] -> Int -> ExpressionT m Expression
equalsConstant es const = do
    let signs = makeSignsFromValue const (length es)
    lits <- mapM ((`addExpression` []) . ELit) es
    addExpression EConjunct (zipWith Var signs (map index lits))

equate :: Monad m => Expression -> Expression -> ExpressionT m Expression
equate a b = do
    addExpression EEquals [Var Pos (index a), Var Pos (index b)]

implicate :: Monad m => Expression -> Expression -> ExpressionT m Expression
implicate a b = do
    addExpression EDisjunct [Var Neg (index a), Var Pos (index b)]

negation :: Monad m => Expression -> ExpressionT m Expression
negation x = do
    addExpression ENot [Var Pos (index x)]

trueExpr :: Monad m => ExpressionT m Expression
trueExpr = addExpression ETrue []

falseExpr :: Monad m => ExpressionT m Expression
falseExpr = addExpression EFalse []

-- Takes an expression tree and paritions it into sets of espressions of the same copy
partitionCopies :: Monad m => Expression -> ExpressionT m ([(Int, Set.Set Expression)])
partitionCopies e = foldrExpression f [(0, Set.empty)] e
    where 
    f e sets@(s:ss) = case operation e of
        ECopy c -> (c, Set.empty) : sets
        _       -> (fst s, Set.insert e (snd s)) : ss
        
toDimacs :: Monad m => Expression -> ExpressionT m (Map.Map (Int, Int) Int, [[Int]])
toDimacs e = do
    copies <- partitionCopies e
    let exprs = concatMap (\(c, es) -> map (\e -> (c, e)) (Set.toList es)) copies
    let eMap = Map.fromList (zip (map (mapSnd index) exprs) [1..])
    dimacs <- concatMapM (exprToDimacs eMap) exprs
    let de = fromJust (Map.lookup (0, index e) eMap)
    return $ (eMap, [de] : dimacs)

exprToDimacs m (c, e) = do
    let ind = fromJust $ Map.lookup (c, (index e)) m
    cs <- mapM (makeChildVar m c) (children e)
    return $ makeDimacs (operation e) ind cs

makeChildVar m c (Var s i) = do
    e <- (liftM fromJust) (lookupExpression i)
    -- If the var is a copy we need to skip past it
    case operation e of
        ECopy c'    -> makeChildVar m c' (head (children e)) --FIXME sign might be wrong
        _           -> return $ Var s (fromJust (Map.lookup (c, i) m))

makeDimacs op i cs = case op of
    ETrue       -> [[i]]
    EFalse      -> [[-i]]
    EConjunct   -> (i : (map (negate . lit) cs)) : (map (\c -> [-i, (lit c)]) cs)
    EDisjunct   -> (-i : map lit cs) : (map (\c -> [i, -(lit c)]) cs)
    EEquals     -> [[-i, -(lit a), (lit b)], [-i, (lit a), -(lit b)],
                    [i, (lit a), (lit b)], [i, -(lit a), -(lit b)]]
    ENot        -> [[-i, -(lit x)], [i, (lit x)]]
    ELit _      -> []
    where
        (x:_)   = cs
        (a:b:_) = cs
    
printExpression :: Monad m => Expression -> ExpressionT m String
printExpression = printExpression' 0 ""

printExpression' tabs s e = do
    cs <- getChildren e
    let signs = map (\c -> if sign c == Pos then "" else "-") (children e)
    pcs <- mapM (uncurry (printExpression' (tabs+1))) (zip signs cs)
    let t = concat (replicate tabs "  ")
    return $ t ++ s ++ case (operation e) of
        ETrue       -> "T"
        EFalse      -> "F"
        EConjunct   -> "conj {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        EDisjunct   -> "disj {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        EEquals     -> "eq {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        ENot        -> "not {\n"++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}" 
        ELit v      -> show v

makeCopy :: Monad m => Expression -> ExpressionT m (Int, Expression)
makeCopy e = do
    m@ExprManager{..} <- get
    let newCopy = copyIndex + 1
    e' <- addExpression (ECopy newCopy) [Var Pos (index e)]
    m' <- get
    put m' { copyIndex = newCopy }
    return (newCopy, e')
    
