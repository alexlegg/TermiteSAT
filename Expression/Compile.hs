module Expression.Compile (
    compile
    ) where

import Control.Monad.State
import Expression.Expression
import Data.EitherR
import qualified Expression.HAST as HAST
import qualified Data.Map as Map

addExpression :: ExprType -> [Expression] -> ExpressionST Expression
addExpression e c = do
    i <- gets maxIndex
    m <- get
    let expr = Expression i e (map index c)
    put m {maxIndex = i+1, exprMap = Map.insert i expr (exprMap m)}
    return $ expr

compileVar (HAST.FVar f) = do
    let v = ExprVar {
        varname = name f,
        varsect = section f,
        bit     = 0,
        rank    = 1
        }
    return $ ELit Pos v

-- |The 'compile' function takes an AST and converts it to an Expression inside the Expressions State Monad
compile :: AST -> ExpressionST Expression

compile HAST.T = do
    return $ Expression 1 ETrue []

compile HAST.F = do
    return $ Expression 2 EFalse []

compile (HAST.Not x) = do
    x' <- compile x
    e <- addExpression ENot [x']
    return e

compile (HAST.And a b) = compile (HAST.Conj [a, b])

compile (HAST.Or a b) = compile (HAST.Disj [a, b])

compile (HAST.Imp a b) = do
    a' <- compile a
    na' <- addExpression ENot [a']
    b' <- compile b
    addExpression EDisjunct [na', b']

compile (HAST.Conj xs) = do
    xs' <- mapM compile xs
    addExpression EConjunct xs'

compile (HAST.Disj xs) = do
    xs' <- mapM compile xs
    addExpression EDisjunct xs'

compile (HAST.XOr a b) = do
    lift $ Left "XOr not implemented"

compile (HAST.XNor a b) = do
    lift $ Left "XNor not implemented"

compile (HAST.Case xs) = do
    lift $ Left "Case not implemented"

compile (HAST.Var x) = do
    x' <- compileVar x
    addExpression x' []

compile (HAST.EqVar a b) = do
    lift $ Left "EqVar not implemented"

compile (HAST.EqConst a b) = do
    lift $ Left "EqConst not implemented"

compile (HAST.Exists _ _) = do
    lift $ Left "Exists not implemented"

compile (HAST.NExists _ _ _) = do
    lift $ Left "NExists not implemented"

compile (HAST.Let _ _) = do
    lift $ Left "Let not implemented"

compile (HAST.LetLit _) = do
    lift $ Left "LetLit not implemented"
