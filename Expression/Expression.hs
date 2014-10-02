module Expression.Expression where

import Control.Monad.State

type ExpressionST = StateT ExprManager IO

data ExprType = ETrue
              | EFalse
              | EConjunct
              | EDisjunct
              | ENot
    deriving (Show, Eq)

data Expression = Expression {
    index           :: Int,
    operation       :: ExprType,
    children        :: [Int]
} deriving (Show)

data ExprManager = ExprManager {
    maxIndex        :: Int,
    exprMap         :: Int
} deriving (Show, Eq)
