{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.SatSolver where

import Foreign
import Foreign.C.Types

data GlucoseSolver

foreign import ccall "glucose_wrapper/glucose_wrapper.h glucose_new"
    c_glucose_new :: IO (Ptr GlucoseSolver)

foreign import ccall "glucose_wrapper/glucose_wrapper.h glucose_delete"
    c_glucose_delete :: IO ()
