{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.Interpolator (
      InterpolantResult(..)
    , InterpolatorST(..)
    , InterpolantState(..)
    , interpolate
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad.State
import qualified Data.Vector.Storable as SV

type InterpolatorST m = StateT InterpolantState m

data PeriploSolver

data ENode

data InterpolantState = InterpolantState Bool

data InterpolantResult = InterpolantResult {
      success       :: Bool
    , interpolant   :: [[Int]]
} deriving (Show, Eq)

interpolate :: Int -> [[Int]] -> [[Int]] -> IO InterpolantResult
interpolate max a b = do
    solver <- liftIO $ c_periplo_new

    liftIO $ c_periplo_delete solver 


    return $ InterpolantResult {
        success = False,
        interpolant = []
    }

addClauseA solver clause = do
    SV.unsafeWith clause (c_periplo_addClause solver True (fromIntegral (SV.length clause)))

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_new"
    c_periplo_new :: IO (Ptr PeriploSolver)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_delete"
    c_periplo_delete :: Ptr PeriploSolver -> IO ()

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_addClause"
    c_periplo_addClause :: Ptr PeriploSolver -> Bool -> CInt -> Ptr CInt -> IO ()

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeTrue"
    c_periplo_enodeTrue :: Ptr PeriploSolver -> Ptr ENode

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeFalse"
    c_periplo_enodeFalse :: Ptr PeriploSolver -> Ptr ENode

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeNot"
    c_periplo_enodeNot :: Ptr PeriploSolver -> Ptr ENode -> Ptr ENode

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeAnd"
    c_periplo_enodeAnd :: Ptr PeriploSolver -> Ptr ENode -> Ptr (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeOr"
    c_periplo_enodeOr :: Ptr PeriploSolver -> Ptr ENode -> Ptr (Ptr ENode)
