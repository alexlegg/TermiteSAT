{-# LANGUAGE RecordWildCards #-}
module Expression.Expression where

import Control.Monad.State
import Control.Monad.Trans.Either
import Control.Monad.Identity
import qualified Data.Map as Map
import Data.List
import qualified Expression.HAST as HAST

data Void
type AST = HAST.AST VarInfo Void Void VarInfo

type ExpressionT m a = StateT ExprManager (EitherT String m) a

throwError :: Monad m => String -> ExpressionT m a
throwError = lift . hoistEither . Left

data ExprType = ETrue
              | EFalse
              | EConjunct
              | EDisjunct
              | EEquals
              | ENot
              | ELit Sign ExprVar
    deriving (Show, Eq)

data ExprVar = ExprVar {
    varname     :: String,
    varsect     :: Section,
    bit         :: Int,
    rank        :: Int
    } deriving (Eq)

instance Show ExprVar where
    show v = let ExprVar{..} = v in varname ++ show rank ++ "[" ++ show bit ++ "]"

data Sign = Pos | Neg deriving (Show, Eq)

data Expression = Expression {
    index           :: Int,
    operation       :: ExprType,
    children        :: [Int]
} deriving (Eq)

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
            ELit Neg v  -> "-" ++ show v

data ExprManager = ExprManager {
    maxIndex        :: Int,
    exprMap         :: Map.Map Int Expression
} deriving (Eq)

instance Show ExprManager where
    show m = let ExprManager{..} = m in
        "maxIndex: " ++ show maxIndex ++
        Map.foldl (\a b -> a ++ "\n" ++ show b) "" exprMap

data Section = StateVar | ContVar | UContVar
    deriving (Show, Eq)

type Slice = Maybe (Int, Int)

data VarInfo = VarInfo {
    name    :: String,
    sz      :: Int,
    section :: Section,
    slice   :: Slice,
    virank  :: Int
} deriving (Show, Eq)

