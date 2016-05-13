module Expression.AST (
      AST
    , VarInfo(..)
    , Slice
    , Section(..)
    , Assignment(..)
    ) where

import qualified Expression.HAST as HAST
import Expression.Expression (Assignment(..), Section(..))

data Void

instance Show Void where
    show _ = "void"

type AST = HAST.AST VarInfo Void Void VarInfo

data VarInfo = VarInfo {
    name    :: String,
    sz      :: Int,
    section :: Section,
    slice   :: Slice,
    virank  :: Int,
    enum    :: Maybe [(String, Int)]
} deriving (Eq)

instance Show VarInfo where
    show v = name v

type Slice = Maybe (Int, Int)

