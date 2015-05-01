{-# LANGUAGE RecordWildCards #-}
module Expression.Compile (
        compile
      , compileVar
      , CompiledSpec(..)
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Data.List
import qualified Data.Map as Map

import qualified Expression.HAST as HAST
import Expression.AST
import Expression.Expression

data CompiledSpec = CompiledSpec {
      t         :: [Expression]
    , useFair   :: Bool
    , cg        :: [Expression]
    , ug        :: [Expression]
    , u         :: [Expression]
    , vc        :: [Expression]
    , vu        :: [Expression]
    , cont      :: [ExprVar]
    , ucont     :: [ExprVar]
    , svars     :: [ExprVar]
    , vinfo     :: [VarInfo]
    }

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . left

compileVar :: VarInfo -> [ExprVar]
compileVar v = map (makeVar v) bits
    where
        bits = case slice v of
                Nothing     -> [0..((sz v)-1)]
                Just (s, e) -> [s..e]

compileHVar (HAST.FVar f) = do
    return $ map (makeVar f) [0..((sz f)-1)]

compileHVar (HAST.EVar _) = do
    throwError "EVar not implemented"

compileHVar (HAST.NVar v) = do
    let bits = case slice v of
                Nothing     -> [0..((sz v)-1)]
                Just (s, e) -> [s..e]
    return $ map (makeVar v) bits

makeVar vi bit = ExprVar {
    varname = name vi,
    varsect = section vi,
    bit     = bit,
    rank    = virank vi,
    ecopy   = 0
    }
    
makeConditions xs = do
    mapM f (tail (inits xs))
    where
        f xs' = do
            let y = last xs'
            let ys = init xs'
            prev <- mapM (\a -> negation a) ys
            conjunct (y : prev)

-- |The 'compile' function takes an AST and converts it to an Expression inside the Expressions State Monad
compile :: MonadIO m => AST -> ExpressionT m Expression

compile HAST.T = do
    trueExpr

compile HAST.F = do
    falseExpr

compile (HAST.Not x) = do
    x' <- compile x
    negation x'

compile (HAST.And a b) = compile (HAST.Conj [a, b])

compile (HAST.Or a b) = compile (HAST.Disj [a, b])

compile (HAST.Imp a b) = do
    a' <- compile a
    b' <- compile b
    implicate a' b'

compile (HAST.Conj xs) = do
    xs' <- mapM compile xs
    conjunct xs'

compile (HAST.Disj xs) = do
    xs' <- mapM compile xs
    disjunct xs'

compile (HAST.XOr a b) = do
    throwError "XOr not implemented"

compile (HAST.XNor a b) = do
    a' <- compile a
    b' <- compile b
    equate a' b'

compile (HAST.Case xs) = do
    let (cs, es) = unzip xs
    cs' <- mapM compile cs
    es' <- mapM compile es
    conds <- makeConditions cs'
    cases <- mapM (\(a, b) -> conjunct [a, b]) (zip conds es')
    disjunct cases

compile (HAST.Var x) = do
    x' <- compileHVar x
    when (length x' /= 1) $ throwError "Var must be of size 1"
    literal (head x')

compile (HAST.EqVar a b) = do
    a' <- compileHVar a
    b' <- compileHVar b
    when (length a' /= length b') $ throwError ("Attempted equality of unequally sized vars (" ++ show a' ++ " & " ++ show b' ++ ")")
    as <- mapM literal a'
    bs <- mapM literal b'
    eqs <- mapM (uncurry equate) (zip as bs)
    conjunct eqs

compile (HAST.EqConst a b) = do
    a' <- compileHVar a
    equalsConstant a' b

compile (HAST.Exists _ _) = do
    throwError "Exists not implemented"

compile (HAST.NExists _ _ _) = do
    throwError "NExists not implemented"

compile (HAST.Let _ _) = do
    throwError "Let not implemented"

compile (HAST.LetLit _) = do
    throwError "LetLit not implemented"
