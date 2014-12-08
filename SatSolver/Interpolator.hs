{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.Interpolator (
      InterpolantResult(..)
    , interpolate
    ) where

data InterpolantResult = InterpolantResult {
      success       :: Bool
    , interpolant   :: [[Int]]
} deriving (Show, Eq)

interpolate :: Int -> [[Int]] -> [[Int]] -> IO InterpolantResult
interpolate max a b = do
    return $ InterpolantResult {
        success = False,
        interpolant = []
    }
