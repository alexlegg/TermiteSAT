module Expression.Expression where

import Control.Monad.State
import qualified Data.Map as Map
import qualified Expression.HAST as HAST

data Void
type AST = HAST.AST VarInfo Void Void VarInfo

type ExpressionST a = StateT ExprManager (Either String) a

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
    } deriving (Show, Eq)

data Sign = Pos | Neg deriving (Show, Eq)

data Expression = Expression {
    index           :: Int,
    operation       :: ExprType,
    children        :: [Int]
} deriving (Show, Eq)

data ExprManager = ExprManager {
    maxIndex        :: Int,
    exprMap         :: Map.Map Int Expression
} deriving (Show, Eq)

data Section = StateVar | ContVar | UContVar
    deriving (Show, Eq)

type Slice = Maybe (Int, Int)

data VarInfo = VarInfo {
    name    :: String,
    sz      :: Int,
    section :: Section,
    slice   :: Slice
} deriving (Show, Eq)

