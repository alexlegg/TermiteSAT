{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.SatSolver (
    satSolve
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad
import Control.Monad.Loops

data GlucoseSolver

satSolve :: Int -> [[Int]] -> IO Bool
satSolve max clauses = do
    solver <- c_glucose_new

    replicateM_ max (c_glucose_addVar solver)

    allM (addClause solver) clauses

    res <- c_solve solver

    c_glucose_delete solver

    return res

addClause solver clause = do
    forM_ clause (c_addClause_addLit solver . fromIntegral)
    c_addClause solver

foreign import ccall "glucose_wrapper/glucose_wrapper.h glucose_new"
    c_glucose_new :: IO (Ptr GlucoseSolver)

foreign import ccall "glucose_wrapper/glucose_wrapper.h glucose_delete"
    c_glucose_delete :: Ptr GlucoseSolver -> IO ()

foreign import ccall "glucose_wrapper/glucose_wrapper.h addVar"
    c_glucose_addVar :: Ptr GlucoseSolver -> IO ()

foreign import ccall "glucose_wrapper/glucose_wrapper.h addClause_addLit"
    c_addClause_addLit :: Ptr GlucoseSolver -> CInt -> IO ()

foreign import ccall "glucose_wrapper/glucose_wrapper.h addClause"
    c_addClause :: Ptr GlucoseSolver -> IO Bool

foreign import ccall "glucose_wrapper/glucose_wrapper.h solve"
    c_solve :: Ptr GlucoseSolver -> IO Bool
