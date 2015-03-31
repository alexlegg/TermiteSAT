{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.SatSolver (
      SatResult(..)
    , unsatisfiable
    , satSolve
    , minimiseCore
    , dumpDimacs
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

satSolve :: Int -> Maybe [Assignment] -> Expression -> SolverT SatResult
satSolve mc a e = do
    maxId       <- liftE $ getMaxId mc
    clauses     <- toDimacs mc e
    assumptions <- liftE $ maybeM [] (mapM (assignmentToVar mc)) a
    let as      = map (\a -> if sign a == Pos then var a else -(var a)) assumptions
    res <- liftIO $ callSolver maxId as clauses
    return res

dumpDimacs :: Int -> Expression -> FilePath -> SolverT ()
dumpDimacs mc e fp = do
    maxId       <- liftE $ getMaxId mc
    clauses     <- toDimacs mc e
    let d       = interMap "\n" (interMap " " show . SV.toList) clauses
    liftIO $ writeFile fp d
    

callSolver max assumptions clauses = do
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

toDimacs mc e = do
    dimacs <- liftE $ getCachedStepDimacs mc e
    return (SV.singleton (fromIntegral (exprIndex e)) : dimacs)

minimiseCore :: GameTree -> Maybe [Assignment] -> Expression -> SolverT (Maybe [Int])
minimiseCore gt a e = do
    maxId       <- liftE $ getMaxId (gtMaxCopy gt)
    clauses     <- toDimacs (gtMaxCopy gt) e
    assumptions <- liftE $ maybeM [] (mapM (assignmentToVar (gtMaxCopy gt))) a
    let as      = map (\a -> if sign a == Pos then var a else -(var a)) assumptions

    forM_ clauses $ \cl -> do
        forM_ (SV.toList cl) $ \l -> do
            when ((abs (fromIntegral l)) > maxId) $ do
                throwError "lit larger than maxid"

    doMinimiseCore maxId as clauses

doMinimiseCore :: Int -> [Int] -> [SV.Vector CInt] -> SolverT (Maybe [Int])
doMinimiseCore max assumptions clauses = do
    solver <- liftIO $ c_glucose_new

    liftIO $ replicateM_ (max+1) (c_glucose_addVar solver)

    liftIO $ addAssumptions solver assumptions

    liftIO $ allM (addClause solver) clauses

    res <- liftIO $ c_solve solver

    if res
    then do
        --SAT, there is no core to find
        liftIO $ c_glucose_delete solver
        return Nothing
    else do
        --UNSAT, try with no core
        conflicts <- liftIO $ getConflicts solver
        liftIO $ c_clearAssumptions solver
        noCore <- liftIO $ c_solve solver

        if noCore
        then do
            liftIO $ addAssumptions solver conflicts
            core_ptr <- liftIO $ c_minimise_core solver

            core <- liftIO $ peekArray0 0 core_ptr
            liftIO $ free core_ptr
            liftIO $ c_glucose_delete solver
            return $ Just (map fromIntegral core)
        else do
            liftIO $ c_glucose_delete solver
            liftIO $ putStrLn "minimise_core -> UNSAT w/ no core"
            return Nothing

addAssumptions solver ass = do
    forM_ ass (c_addAssumption solver . fromIntegral)

addClause solver clause = do
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
