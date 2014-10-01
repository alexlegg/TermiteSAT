module Expression.Expression where

import Control.Monad.State

type ExpressionST = StateT ExprManager IO

data ExprManager = ExprManager {
    maxIndex        :: Int,
    exprMap         :: Int
} deriving (Show, Eq)
