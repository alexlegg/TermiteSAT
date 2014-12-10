{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.Interpolator (
      InterpolantResult(..)
    , interpolate
    ) where

import Foreign
import Foreign.C.Types

data PeriploSolver

data InterpolantResult = InterpolantResult {
      success       :: Bool
    , interpolant   :: [[Int]]
} deriving (Show, Eq)

interpolate :: Int -> [[Int]] -> [[Int]] -> IO InterpolantResult
interpolate max a b = do
    solver <- c_periplo_new

    c_periplo_delete solver 

    return $ InterpolantResult {
        success = False,
        interpolant = []
    }

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_new"
    c_periplo_new :: IO (Ptr PeriploSolver)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_delete"
    c_periplo_delete :: Ptr PeriploSolver -> IO ()
