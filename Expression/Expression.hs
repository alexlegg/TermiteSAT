{-# LANGUAGE RecordWildCards #-}
module Expression.Expression (
      ExpressionT(..)
    , ExprVar(..)
    , Expression
    , Section(..)
    , Sign(..)
    , Var(..)
    , Assignment(..)

    , exprIndex
    , flipSign
    , emptyManager
    , getChildren
    , lookupExpression
    , lookupVar
    , traverseExpression
    , foldlExpression
    , foldrExpression
    , unrollExpression
    , setRank
    , setHatVar
    , conjunct
    , disjunct
    , equate
    , implicate
    , negation
    , equalsConstant
    , trueExpr
    , falseExpr
    , literal
    , toDimacs
    , makeCopy
    , printExpression
    , makeAssignment
    , assignmentToExpression
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

flipSign Pos = Neg
flipSign Neg = Pos

data Expr   = ETrue
            | EFalse
            | ELit ExprVar
            | ENot Var
            | ECopy Int Var
            | EEquals Var Var
            | EConjunct [Var]
            | EDisjunct [Var]
            deriving (Eq, Ord, Show)

data Expression = Expression {
      index     :: Int
    , expr      :: Expr
    } deriving (Eq, Ord, Show)

exprIndex :: Expression -> Int
exprIndex = index

children :: Expr -> [Var]
children (ETrue)            = []
children (EFalse)           = []
children (ELit _)           = []
children (ENot v)           = [v]
children (ECopy c v)        = [v]
children (EEquals x y)      = [x, y]
children (EConjunct vs)     = vs
children (EDisjunct vs)     = vs

data ExprManager = ExprManager {
    maxIndex        :: Int,
    exprMap         :: Map.Map Int Expr,
    indexMap        :: Map.Map Expr Int,
    copyIndex       :: Int
} deriving (Eq)

instance Show ExprManager where
    show m = let ExprManager{..} = m in
        "maxIndex: " ++ show maxIndex ++
        Map.foldl (\a b -> a ++ "\n" ++ show b) "" exprMap

data Section = StateVar | ContVar | UContVar | HatVar
    deriving (Show, Eq, Ord)

data Assignment = Assignment Sign ExprVar deriving (Eq, Ord)

emptyManager = ExprManager { maxIndex = 3, exprMap = Map.empty, indexMap = Map.empty, copyIndex = 0 }

addExpression :: Monad m => Expr -> ExpressionT m Expression
addExpression e = do
    m@ExprManager{..} <- get
    case Map.lookup e indexMap of
        Nothing -> do
            let i = maxIndex
            put m {
                maxIndex    = maxIndex+1,
                exprMap     = Map.insert i e exprMap,
                indexMap    = Map.insert e i indexMap}
            return $ Expression { index = i, expr = e }
        Just i -> do
            return $ Expression { index = i, expr = e }

lookupExpression :: Monad m => Int -> ExpressionT m (Maybe Expression)
lookupExpression i = do
    ExprManager{..} <- get
    case Map.lookup i exprMap of
        Nothing     -> return Nothing
        (Just exp)  -> return $ Just (Expression { index = i, expr = exp })

lookupVar :: Monad m => ExprVar -> ExpressionT m (Maybe Expression)
lookupVar v = do
    m@ExprManager{..} <- get
    case Map.lookup (ELit v) indexMap of
        Nothing -> return Nothing
        Just i  -> return $ Just (Expression { index = i, expr = (ELit v) })

getChildren :: Monad m => Expression -> ExpressionT m [Expression]
getChildren e = do
    es <- mapM (lookupExpression . var) (children (expr e))
    return (catMaybes es)

foldlExpression :: Monad m => (a -> Expression -> a) -> a -> Expression -> ExpressionT m a
foldlExpression f x e = do
    cs <- getChildren e
    foldlM (foldlExpression f) (f x e) cs

foldrExpression :: Monad m => (Expression -> a -> a) -> a -> Expression -> ExpressionT m a
foldrExpression f x e = do
    cs <- getChildren e
    foldlM (foldrExpression f) (f e x) cs

traverseExpression :: Monad m => (ExprVar -> ExprVar) -> Expression -> ExpressionT m Expression
traverseExpression f e = do
    let signs = map sign (children (expr e))
    cs <- getChildren e
    cs' <- mapM (traverseExpression f) cs
    let cs'' = map (uncurry Var) (zip signs (map index cs'))
    addExpression (applyToVars f (expr e)) -- WRONG
    where
        applyToVars f (ELit v)  = ELit (f v)
        applyToVars f x         = x

setRank :: Monad m => Int -> Expression -> ExpressionT m Expression
setRank r = traverseExpression (setVarRank r)
    
setVarRank r v = v {rank = r}

setHatVar :: Monad m => Expression -> ExpressionT m Expression
setHatVar = traverseExpression setVarHat

setVarHat v = if varsect v == UContVar || varsect v == ContVar
                then v {varname = varname v ++ "_hat", varsect = HatVar}
                else v

unrollExpression :: Monad m => Expression -> ExpressionT m Expression
unrollExpression = traverseExpression shiftVar

shiftVar v = v {rank = rank v + 1}

liftConjuncts Expression { expr = (EConjunct vs) }  = vs
liftConjuncts Expression { index = i }              = [Var Pos i]

liftDisjuncts Expression { expr = (EDisjunct vs) }  = vs
liftDisjuncts Expression { index = i }              = [Var Pos i]

-- |The 'conjunct' function takes a list of Expressions and produces one conjunction Expression
conjunct :: Monad m => [Expression] -> ExpressionT m Expression
conjunct []     = addExpression EFalse
conjunct (e:[]) = return e
conjunct es     = addExpression (EConjunct (concatMap liftConjuncts es))

-- |The 'disjunct' function takes a list of Expressions and produces one disjunction Expression
disjunct :: Monad m => [Expression] -> ExpressionT m Expression
disjunct []     = addExpression ETrue
disjunct (e:[]) = return e
disjunct es     = addExpression (EDisjunct (concatMap liftDisjuncts es))

makeSignsFromValue :: Int -> Int -> [Sign]
makeSignsFromValue v sz = map f [0..(sz-1)]
    where
        f b = if testBit v b then Pos else Neg

equalsConstant :: Monad m => [ExprVar] -> Int -> ExpressionT m Expression
equalsConstant es const = do
    let signs = makeSignsFromValue const (length es)
    lits <- mapM literal es
    addExpression (EConjunct (zipWith Var signs (map index lits)))

equate :: Monad m => Expression -> Expression -> ExpressionT m Expression
equate a b = do
    addExpression (EEquals (Var Pos (index a)) (Var Pos (index b)))

implicate :: Monad m => Expression -> Expression -> ExpressionT m Expression
implicate a b = do
    addExpression (EDisjunct [Var Neg (index a), Var Pos (index b)])

negation :: Monad m => Expression -> ExpressionT m Expression
negation x = do
    addExpression (ENot (Var Pos (index x)))

trueExpr :: Monad m => ExpressionT m Expression
trueExpr = addExpression ETrue

falseExpr :: Monad m => ExpressionT m Expression
falseExpr = addExpression EFalse

literal :: Monad m => ExprVar -> ExpressionT m Expression
literal = addExpression . ELit

-- Takes an expression tree and paritions it into sets of espressions of the same copy
partitionCopies :: Monad m => Expression -> ExpressionT m ([(Int, Set.Set Expression)])
partitionCopies e = foldrExpression f [(0, Set.empty)] e
    where 
    f e sets@(s:ss) = case expr e of
        (ECopy c _) -> (c, Set.empty) : sets
        _           -> (fst s, Set.insert e (snd s)) : ss

baseExpr e = case expr e of
    (ECopy c v) -> (c, var v)
    _           -> (0, index e)
        
toDimacs :: Monad m => Expression -> ExpressionT m (Map.Map (Int, Int) Int, [[Int]])
toDimacs e = do
    copies <- partitionCopies e
    let exprs = concatMap (\(c, es) -> map (\e -> (c, e)) (Set.toList es)) copies
    let dMap = Map.fromList (zip (map (mapSnd index) exprs) [1..])
    dimacs <- concatMapM (exprToDimacs dMap) exprs
    let (Just de) = Map.lookup (baseExpr e) dMap
    return $ (dMap, [de] : dimacs)

exprToDimacs m (c, e) = do
    let ind = fromJust $ Map.lookup (c, (index e)) m
    cs <- mapM (makeChildVar m c) (children (expr e))
    return $ makeDimacs (expr e) ind cs

makeChildVar m c (Var s i) = do
    e <- (liftM fromJust) (lookupExpression i)
    -- If the var is a copy we need to skip past it
    case expr e of
        (ECopy c' v)    -> do
            (Var s' i') <- makeChildVar m c' v
            return $ Var (if (s == s') then Pos else Neg) i'
        _               -> return $ Var s (fromJust (Map.lookup (c, i) m))

makeDimacs e i cs = case e of
    (ETrue)         -> [[i]]
    (EFalse)        -> [[-i]]
    (ENot _)        -> [[-i, -(lit x)], [i, (lit x)]]
    (ELit _)        -> []
    (EEquals _ _)   -> [[-i, -(lit a), (lit b)], [-i, (lit a), -(lit b)],
                        [i, (lit a), (lit b)], [i, -(lit a), -(lit b)]]
    (EConjunct _)   -> (i : (map (negate . lit) cs)) : (map (\c -> [-i, (lit c)]) cs)
    (EDisjunct _)   -> (-i : map lit cs) : (map (\c -> [i, -(lit c)]) cs)
    where
        (x:_)   = cs
        (a:b:_) = cs
    
printExpression :: Monad m => Expression -> ExpressionT m String
printExpression = printExpression' 0 ""

printExpression' tabs s e = do
    cs <- getChildren e
    let signs = map (\c -> if sign c == Pos then "" else "-") (children (expr e))
    pcs <- mapM (uncurry (printExpression' (tabs+1))) (zip signs cs)
    let t = concat (replicate tabs "  ")
    return $ t ++ s ++ case expr e of
        (ETrue)         -> "T"
        (EFalse)        -> "F"
        (EConjunct _)   -> "conj {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        (EDisjunct _)   -> "disj {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        (EEquals _ _)   -> "eq {\n" ++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}"
        (ENot _)        -> "not {\n"++ intercalate ",\n" pcs ++ "\n" ++ t ++ "}" 
        (ECopy c _)     -> "copy " ++ show c ++ " {" ++ head pcs ++ "}"
        (ELit v)        -> show v

makeCopy :: Monad m => Expression -> ExpressionT m (Int, Expression)
makeCopy e = do
    m@ExprManager{..} <- get
    let newCopy = copyIndex + 1
    put m { copyIndex = newCopy }
    e' <- addExpression (ECopy newCopy (Var Pos (index e)))
    return (newCopy, e')
    
-- |Contructs an assignment from a model-var pair
makeAssignment :: (Int, ExprVar) -> Assignment
makeAssignment (m, v) = Assignment (if m > 0 then Pos else Neg) v

-- |Constructs an expression from assignments
assignmentToExpression :: Monad m => [Assignment] -> ExpressionT m Expression
assignmentToExpression as = do
    vs <- mapM f as
    addExpression (EConjunct vs)
    where
        f (Assignment s v) = do
            e <- addExpression (ELit v)
            return $ Var s (index e)

