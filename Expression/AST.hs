module Expression.AST (
      AST(..)
    , VarInfo(..)
    , Slice(..)
    , Section(..)
    , Assignment(..)
    ) where

import qualified Expression.HAST as HAST
import Expression.Expression (Assignment(..), Section(..))

data Void
type AST = HAST.AST VarInfo Void Void VarInfo

data VarInfo = VarInfo {
    name    :: String,
    sz      :: Int,
    section :: Section,
    slice   :: Slice,
    virank  :: Int,
    enum    :: Maybe [(String, Int)]
} deriving (Show, Eq)

type Slice = Maybe (Int, Int)

