{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.SatSolver (
    SatResult(..),
    satSolve
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad
import Control.Monad.Loops

data GlucoseSolver

data SatResult = SatResult {
    satisfiable     :: Bool,
    model           :: Maybe [Int],
    conflicts       :: Maybe [Int]
    } deriving (Show, Eq)

satSolve :: Int -> [Int] -> [[Int]] -> IO SatResult
satSolve max assumptions clauses = do
    solver <- c_glucose_new

    -- Add one var so we can ignore 0
    c_glucose_addVar solver

    -- Add enough vars for our clause set
    replicateM_ max (c_glucose_addVar solver)

    -- Add assumptions
    addAssumptions solver assumptions

    -- Add the clauses
    allM (addClause solver) clauses

    -- Get the result
    res <- c_solve solver
    model <- if res 
        then liftM Just $ getModel solver 
        else return Nothing

    conflicts <- if not res
        then liftM Just $ getConflicts solver
        else return Nothing

    -- Clean up
    c_glucose_delete solver

    return $ SatResult {
        satisfiable = res,
        model = fmap (map fromIntegral) model,
        conflicts = fmap (map fromIntegral) conflicts
        }

addAssumptions solver ass = do
    forM_ ass (c_addAssumption solver . fromIntegral)

addClause solver clause = do
    forM_ clause (c_addClause_addLit solver . fromIntegral)
    c_addClause solver

getModel solver = do
    model <- c_model solver
    res <- peekArray0 0 model
    free model
    return res

getConflicts solver = do
    conflicts <- c_conflicts solver
    res <- peekArray0 0 conflicts
    free conflicts
    return res

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h glucose_new"
    c_glucose_new :: IO (Ptr GlucoseSolver)

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h glucose_delete"
    c_glucose_delete :: Ptr GlucoseSolver -> IO ()

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h addVar"
    c_glucose_addVar :: Ptr GlucoseSolver -> IO ()

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h addAssumption"
    c_addAssumption :: Ptr GlucoseSolver -> CInt -> IO ()

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h addClause_addLit"
    c_addClause_addLit :: Ptr GlucoseSolver -> CInt -> IO ()

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h addClause"
    c_addClause :: Ptr GlucoseSolver -> IO Bool

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h solve"
    c_solve :: Ptr GlucoseSolver -> IO Bool

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h model"
    c_model :: Ptr GlucoseSolver -> IO (Ptr CInt)

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h conflicts"
    c_conflicts :: Ptr GlucoseSolver -> IO (Ptr CInt)
