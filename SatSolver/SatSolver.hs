{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.SatSolver (
      SatResult(..)
    , unsatisfiable
    , satSolve
    , minimiseCore
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Loops
import qualified Data.Vector.Storable as SV
import qualified Data.IntSet as ISet
import Data.Maybe
import Expression.Expression
import Synthesise.SolverT
import Synthesise.GameTree
import Utils.Utils

data GlucoseSolver

data SatResult = SatResult {
    satisfiable     :: Bool,
    model           :: Maybe [Int],
    conflicts       :: Maybe [Int]
    } deriving (Show, Eq)

unsatisfiable :: SatResult -> Bool
unsatisfiable = not . satisfiable

var (Var _ v)   = v
sign (Var s _)  = s

satSolve :: GameTree -> Maybe [Assignment] -> Expression -> SolverT SatResult
satSolve gt a e = do
    maxId       <- liftE $ getMaxId
    clauses     <- toDimacs gt e
    assumptions <- liftE $ maybeM [] (mapM assignmentToVar) a
    let as      = map (\a -> if sign a == Pos then var a else -(var a)) assumptions

    liftIO $ callSolver maxId as clauses

callSolver max assumptions clauses = do
    solver <- c_glucose_new


    -- Add one var so we can ignore 0
    c_glucose_addVar solver

    -- Add enough vars for our clause set
    replicateM_ max (c_glucose_addVar solver)

    -- Add assumptions
    addAssumptions solver assumptions

    -- Add the clauses
    allM (addClause2 solver) clauses

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

toDimacs gt e = do
    dimacs <- liftE $ getCachedStepDimacs (gtMaxCopy gt) e
    return (SV.singleton (fromIntegral (exprIndex e)) : dimacs)

minimiseCore :: GameTree -> Maybe [Assignment] -> Expression -> SolverT (Maybe [Int])
minimiseCore gt a e = do
    maxId       <- liftE $ getMaxId
    clauses     <- toDimacs gt e
    assumptions <- liftE $ maybeM [] (mapM assignmentToVar) a
    let as      = map (\a -> if sign a == Pos then var a else -(var a)) assumptions

    liftIO $ doMinimiseCore maxId as clauses

doMinimiseCore max assumptions clauses = do
    solver <- c_glucose_new

    replicateM_ (max+1) (c_glucose_addVar solver)

    addAssumptions solver assumptions

    allM (addClause2 solver) clauses

    res <- c_solve solver

    if res
    then do
        --SAT, there is no core to find
        c_glucose_delete solver
        return Nothing
    else do
        --UNSAT, try with no core
        conflicts <- getConflicts solver
        c_clearAssumptions solver
        noCore <- c_solve solver

        if noCore
        then do
            addAssumptions solver conflicts
            core_ptr <- c_minimise_core solver

            core <- peekArray0 0 core_ptr
            free core_ptr
            c_glucose_delete solver
            return $ Just (map fromIntegral core)
        else do
            c_glucose_delete solver
            return Nothing

addAssumptions solver ass = do
    forM_ ass (c_addAssumption solver . fromIntegral)

addClause solver clause = do
    forM_ clause (c_addClause_addLit solver . fromIntegral)
    c_addClause solver

addClause2 solver clause = do
    SV.unsafeWith clause (c_addClauseVector solver (fromIntegral (SV.length clause)))

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

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h clearAssumptions"
    c_clearAssumptions :: Ptr GlucoseSolver -> IO ()

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h addClause_addLit"
    c_addClause_addLit :: Ptr GlucoseSolver -> CInt -> IO ()

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h addClause"
    c_addClause :: Ptr GlucoseSolver -> IO Bool

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h addClauseVector"
    c_addClauseVector :: Ptr GlucoseSolver -> CInt -> Ptr CInt -> IO Bool

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h solve"
    c_solve :: Ptr GlucoseSolver -> IO Bool

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h minimise_core"
    c_minimise_core :: Ptr GlucoseSolver -> IO (Ptr CInt)

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h model"
    c_model :: Ptr GlucoseSolver -> IO (Ptr CInt)

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h conflicts"
    c_conflicts :: Ptr GlucoseSolver -> IO (Ptr CInt)
