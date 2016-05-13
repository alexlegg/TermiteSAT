{-# LANGUAGE RecordWildCards #-}
module Expression.Compile (
        compile
      , compileAIG
      , compileVar
      , compileInit
      , CompiledSpec(..)
    ) where

import Control.Monad.State
import Control.Monad.Trans.Either
import Data.List
import Data.Maybe

import qualified Expression.HAST as HAST
import Expression.AST
import Expression.Expression
import Utils.Utils

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

compileInit :: [(VarInfo, Int)] -> [Assignment]
compileInit []              = []
compileInit ((v, val):vs)   = zipWith Assignment signs (map (makeVar v) bits) ++ compileInit vs
    where
        bits = case slice v of
                Nothing     -> [0..((sz v)-1)]
                Just (s, e) -> [s..e]
        signs = makeSignsFromValue val (length bits)

compileHVar :: MonadIO m => HAST.ASTVar VarInfo t VarInfo -> ExpressionT m [ExprVar]
compileHVar (HAST.FVar f) = do
    return $ map (makeVar f) [0..((sz f)-1)]

compileHVar (HAST.EVar _) = do
    throwError "EVar not implemented"

compileHVar (HAST.NVar v) = do
    let bits = case slice v of
                Nothing     -> [0..((sz v)-1)]
                Just (s, e) -> [s..e]
    return $ map (makeVar v) bits

makeVar :: VarInfo -> Int -> ExprVar
makeVar vi bit = ExprVar {
    varname = name vi,
    varsect = section vi,
    bit     = bit,
    rank    = virank vi,
    ecopy   = 0
    }
    
makeConditions :: MonadIO m => [Expression] -> ExpressionT m [Expression]
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

compile (HAST.XOr _ _) = do
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

compileAIG :: MonadIO m => ([(AST, Int)], [(Int, Int, Int)]) -> [(Int, AST)] -> ExpressionT m [Expression]
compileAIG (latches, gates) vMap = do
    cGates      <- compileGates vMap [] gates
    cLatches    <- mapM (mapSndM (aigToExpression vMap cGates)) latches
    mapM latchToExpression cLatches

aigVar :: Int -> Int
aigVar x    | odd x     = x - 1
            | otherwise = x

aigSign :: Int -> Bool
aigSign x   | odd x     = False
            | otherwise = True

compileGates :: MonadIO m => [(Int, AST)] -> [(Int, Expression)] -> [(Int, Int, Int)] -> ExpressionT m [(Int, Expression)]
compileGates vMap done gates = do
    done' <- foldM (compileGate vMap) done gates
    let gates' = filter (isNothing . (`lookup` done) . fst3) gates
    if null gates'
        then return done'
        else compileGates vMap done' gates'

compileGate :: MonadIO m => [(Int, AST)] -> [(Int, Expression)] -> (Int, Int, Int) -> ExpressionT m [(Int, Expression)]
compileGate vMap done (i, a, b) = do
    ae <- aigToExpression vMap done a
    be <- aigToExpression vMap done b

    if isJust ae && isJust be
        then do
            c <- conjunct [fromJust ae, fromJust be]
            return ((i, c) : done)
        else return done

aigToExpression :: MonadIO m => [(Int, AST)] -> [(Int, Expression)] -> Int -> ExpressionT m (Maybe Expression)
aigToExpression _ _ 0 = do
    f <- falseExpr
    return (Just f)
aigToExpression _ _ 1 = do
    t <- trueExpr
    return (Just t)
aigToExpression vMap done v = do
    case (lookup (aigVar v) done) of
        Just e -> do
            s <- if aigSign v
                then return e
                else negation e
            return (Just s)
        Nothing -> case (lookup (aigVar v) vMap) of
            (Just (HAST.Var x)) -> do
                x'  <- compileHVar x
                when (length x' /= 1) $ throwError "Var must be of size 1"
                l   <- literal (head x')
                s <- if aigSign v
                    then return l
                    else negation l
                return (Just s)
            _       -> return Nothing

latchToExpression :: (MonadIO m) => (AST, Maybe Expression) -> ExpressionT m Expression
latchToExpression (HAST.Var v, e) = do
    v' <- compileHVar v
    when (length v' /= 1) $ throwError "Var must be of size 1"
    l   <- literal (head v')
    when (isNothing e) $ throwError $ "Could not compile latch"
    equate l (fromJust e)
latchToExpression _ = throwError "Latch is not a Var"
