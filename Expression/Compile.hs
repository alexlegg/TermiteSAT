module Expression.Compile (
    compile
    ) where

import Control.Monad.State
import Data.EitherR
import Data.Bits (testBit)
import Data.List
import qualified Data.Map as Map

import qualified Expression.HAST as HAST
import Expression.Expression

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
    return [v]

compileVar (HAST.EVar _) = do
    lift $ Left "EVar not implemented"

compileVar (HAST.NVar v) = do
    let bits = case slice v of
                Nothing     -> [0..((sz v)-1)]
                Just (s, e) -> [s..e]
    return $ map (makeVar v 0) bits

makeVar vi rank bit = ExprVar {
    varname = name vi,
    varsect = section vi,
    bit     = bit,
    rank    = rank
    }
    
makeSignsFromValue :: Int -> Int -> [Sign]
makeSignsFromValue v sz = map f [0..(sz-1)]
    where
        f b = if testBit v b then Pos else Neg

makeConditions xs = do
    mapM f (inits xs)
    where
        f xs' = do
            let x = last xs'
            let xs = init xs
            prev <- mapM (\a -> addExpression ENot [a]) xs
            addExpression EConjunct (x : prev)

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
    let (cs, es) = unzip xs
    cs' <- mapM compile cs
    es' <- mapM compile es
    conds <- makeConditions cs'
    cases <- mapM (\(a, b) -> addExpression EConjunct [a, b]) (zip conds es')
    addExpression EDisjunct cases

compile (HAST.Var x) = do
    x' <- compileVar x
    --addExpression x' []
    lift $ Left "Var not implemented"

compile (HAST.EqVar a b) = do
    a' <- compileVar a
    b' <- compileVar b
    when (length a' /= length b') $ lift $ Left "Attempted equality of unequally sized vars"
    as <- mapM ((`addExpression` []) . (ELit Pos)) a'
    bs <- mapM ((`addExpression` []) . (ELit Pos)) b'
    let cs = [[a, b] | a <- as, b <- bs]
    eqs <- mapM (addExpression EEquals) cs
    addExpression EConjunct eqs

compile (HAST.EqConst a b) = do
    a' <- compileVar a
    let signs = makeSignsFromValue b (length a')
    let mkLit (s, v) = ELit s v
    lits <- mapM ((`addExpression` []) . mkLit) (zip signs a')
    addExpression EConjunct lits

compile (HAST.Exists _ _) = do
    lift $ Left "Exists not implemented"

compile (HAST.NExists _ _ _) = do
    lift $ Left "NExists not implemented"

compile (HAST.Let _ _) = do
    lift $ Left "Let not implemented"

compile (HAST.LetLit _) = do
    lift $ Left "LetLit not implemented"
