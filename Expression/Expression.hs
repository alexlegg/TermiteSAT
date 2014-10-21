{-# LANGUAGE RecordWildCards #-}
module Expression.Expression (
      ExpressionT(..)
    , ExprType(..)
    , ExprVar(..)
    , Expression(..)
    , Section(..)

    , emptyManager
    , addExpression
    , getChildren
    , lookupExpression
    , getMaxIndex
    , traverseExpression
    , foldlExpression
    , foldrExpression
    , unrollExpression
    , conjunct
    , disjunct
    , equate
    , implicate
    , negation
    , equalsConstant
    , trueExpr
    , falseExpr
    , toDimacs
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Bits (testBit)
import Data.Foldable (foldlM)
import Data.Maybe

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
    deriving (Show, Eq, Ord)

data ExprVar = ExprVar {
    varname     :: String,
    varsect     :: Section,
    bit         :: Int,
    rank        :: Int
    } deriving (Eq, Ord)

instance Show ExprVar where
    show v = let ExprVar{..} = v in varname ++ show rank ++ "[" ++ show bit ++ "]"

data Var = Var Sign Int deriving (Show, Eq, Ord)

var (Var _ v)   = v
sign (Var s _)  = s
lit (Var Pos v) = v
lit (Var Neg v) = -v

data Sign = Pos | Neg deriving (Show, Eq, Ord)

data Expression = Expression {
    index           :: Int,
    operation       :: ExprType,
    children        :: [Var]
}

instance Eq Expression where
    x == y      = operation x == operation y && children x == children y

instance Ord Expression where
    x <= y      = operation x <= operation y && children x <= children y

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
    indexMap        :: Map.Map Expression Int
} deriving (Eq)

instance Show ExprManager where
    show m = let ExprManager{..} = m in
        "maxIndex: " ++ show maxIndex ++
        Map.foldl (\a b -> a ++ "\n" ++ show b) "" exprMap

data Section = StateVar | ContVar | UContVar
    deriving (Show, Eq, Ord)

emptyManager = ExprManager { maxIndex = 3, exprMap = Map.empty, indexMap = Map.empty }

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
            return $ expr

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
    let x' = foldl f x cs
    foldlM (foldlExpression f) x' cs

foldrExpression :: Monad m => (Expression -> a -> a) -> a -> Expression -> ExpressionT m a
foldrExpression f x e = do
    cs <- getChildren e
    let x' = foldr f x cs
    foldlM (foldrExpression f) x' cs

traverseExpression :: Monad m => (ExprType -> ExprType) -> Expression -> ExpressionT m Expression
traverseExpression f e = do
    cs <- getChildren e
    cs' <- mapM (traverseExpression f) cs
    addExpression (f (operation e)) (map (Var Pos . index) cs')

unrollExpression :: Monad m => Expression -> ExpressionT m Expression
unrollExpression = traverseExpression shiftVar

shiftVar (ELit v)   = ELit (v {rank = rank v + 1})
shiftVar x          = x

-- |The 'conjunct' function takes a list of Expressions and produces one conjunction Expression
conjunct :: Monad m => [Expression] -> ExpressionT m Expression
conjunct es = do
    case length es of
        0 -> addExpression EFalse []
        1 -> return (head es)
        _ -> addExpression EConjunct (map (Var Pos . index) es)

-- |The 'disjunct' function takes a list of Expressions and produces one disjunction Expression
disjunct :: Monad m => [Expression] -> ExpressionT m Expression
disjunct es = do
    case length es of
        0 -> addExpression ETrue []
        1 -> return (head es)
        _ -> addExpression EDisjunct (map (Var Pos . index) es)

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
    addExpression EEquals [Var Neg (index a), Var Pos (index b)]

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

toDimacs :: Monad m => Expression -> ExpressionT m [[Int]]
toDimacs e = do
    exprs <- foldrExpression Set.insert Set.empty e
    return $ concatMap exprToDimacs (Set.toList exprs)

exprToDimacs e = case (operation e) of
    ETrue       -> [[1]]
    EFalse      -> [[-2]]
    EConjunct   -> (i : (map (negate . lit) cs)) : (map (\c -> [-i, (lit c)]) cs)
    EDisjunct   -> (-i : map lit cs) : (map (\c -> [i, -(lit c)]) cs)
    EEquals     -> [[-i, -(lit a), (lit b)], [-i, (lit a), -(lit b)],
                    [i, (lit a), (lit b)], [i, -(lit a), -(lit b)]]
    ENot        -> [[-i, -(lit x)], [i, (lit x)]]
    ELit _      -> []
    where
        i           = index e
        cs          = children e
        (x:_)       = children e
        (a:b:_)     = children e
