{-# LANGUAGE RecordWildCards #-}
module Expression.Expression (
      ExpressionT(..)
    , ExprType(..)
    , ExprVar(..)
    , Expression(..)
    , Section(..)
    , Sign(..)

    , emptyManager
    , addExpression
    , getChildren
    , getExpression
    , traverseExpression
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import qualified Data.Map as Map
import Data.List
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
              | ELit Sign ExprVar
    deriving (Show, Eq, Ord)

data ExprVar = ExprVar {
    varname     :: String,
    varsect     :: Section,
    bit         :: Int,
    rank        :: Int
    } deriving (Eq, Ord)

instance Show ExprVar where
    show v = let ExprVar{..} = v in varname ++ show rank ++ "[" ++ show bit ++ "]"

data Sign = Pos | Neg deriving (Show, Eq, Ord)

data Expression = Expression {
    index           :: Int,
    operation       :: ExprType,
    children        :: [Int]
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
            ELit Pos v  -> show v
            ELit Neg v  -> '-' : show v

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

addExpression :: Monad m => ExprType -> [Expression] -> ExpressionT m Expression
addExpression e c = do
    m@ExprManager{..} <- get
    let expr = Expression maxIndex e (map index c)
    case Map.lookup expr indexMap of
        Nothing -> do
            put m {
                maxIndex    = maxIndex+1,
                exprMap     = Map.insert maxIndex expr exprMap,
                indexMap    = Map.insert expr maxIndex indexMap}
            return $ expr

        Just i -> do
            return $ fromJust (Map.lookup i exprMap)

getExpression :: Monad m => Int -> ExpressionT m (Maybe Expression)
getExpression i = do
    ExprManager{..} <- get
    return $ Map.lookup i exprMap

getChildren :: Monad m => Expression -> ExpressionT m [Expression]
getChildren e = do
    es <- mapM getExpression (children e)
    return (catMaybes es)

traverseExpression :: Monad m => (Expression -> Expression) -> Expression -> ExpressionT m Expression
traverseExpression f e = do
    cs <- getChildren e
    cs' <- mapM (traverseExpression f) cs
    return $ f (e {children = map index cs'})
