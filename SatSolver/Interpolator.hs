{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.Interpolator (
      InterpolantResult(..)
    , interpolate
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad.State

type InterpolatorST m = StateT PeriploSolver m

data PeriploSolver

data InterpolantResult = InterpolantResult {
      success       :: Bool
    , interpolant   :: [[Int]]
} deriving (Show, Eq)

interpolate :: MonadIO m => Int -> [[Int]] -> [[Int]] -> InterpolatorST m InterpolantResult
interpolate max a b = do
    solver <- liftIO $ c_periplo_new

    liftIO $ c_periplo_delete solver 

    return $ InterpolantResult {
        success = False,
        interpolant = []
    }

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_new"
    c_periplo_new :: IO (Ptr PeriploSolver)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_delete"
    c_periplo_delete :: Ptr PeriploSolver -> IO ()
