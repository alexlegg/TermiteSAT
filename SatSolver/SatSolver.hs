{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.SatSolver (
      SatResult(..)
    , unsatisfiable
    , satSolve
    , minimiseCore
    , dumpDimacs
    , timeInSAT
    , totalSATCalls
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Loops
import qualified Data.Vector.Storable as SV
import System.TimeIt
import Data.IORef
import System.IO.Unsafe

import Utils.Utils
import Synthesise.SolverT
import Expression.Expression

data GlucoseSolver

data SatResult = SatResult {
    satisfiable     :: Bool,
    model           :: Maybe [Int],
    conflicts       :: Maybe [Int]
    } deriving (Show, Eq)

totalTime :: IORef Double
{-# NOINLINE totalTime #-}
totalTime = unsafePerformIO (newIORef 0)

totalCalls :: IORef Int
{-# NOINLINE totalCalls #-}
totalCalls = unsafePerformIO (newIORef 0)

timeInSAT :: IO Double
timeInSAT = do
    t <- readIORef totalTime
    writeIORef totalTime 0
    return t

totalSATCalls :: IO Int
totalSATCalls = do
    c <- readIORef totalCalls
    writeIORef totalCalls 0
    return c

unsatisfiable :: SatResult -> Bool
unsatisfiable = not . satisfiable

var :: Var -> Int
var (Var _ v)   = v

sign :: Var -> Sign
sign (Var s _)  = s

satSolve :: Int -> Maybe [Assignment] -> Expression -> SolverT SatResult
satSolve mc a e = do
    maxId       <- liftE $ getMaxId mc
    clauses     <- toDimacs mc e
    assumptions <- liftE $ maybeM [] (mapM (assignmentToVar mc)) a
    let as      = map (\x -> if sign x == Pos then var x else -(var x)) assumptions

    (time, res) <- liftIO $ timeItT $ callSolver maxId as clauses
    liftIO $ modifyIORef totalTime (time +)
    liftIO $ modifyIORef totalCalls (1 +)

    return res

dumpDimacs :: Int -> Expression -> FilePath -> SolverT ()
dumpDimacs mc e fp = do
    maxId       <- liftE $ getMaxId mc
    clauses     <- toDimacs mc e
    let p       = "p cnf " ++ (show maxId) ++ " " ++ (show (length clauses)) ++ "\n"
    let d       = concatMap (\cs -> (interMap " " show (SV.toList cs)) ++ " 0\n") clauses
    liftIO $ writeFile fp (p ++ d)
    

callSolver :: Int -> [Int] -> [SV.Vector CInt] -> IO SatResult
callSolver maxId assumptions clauses = do
    solver <- c_glucose_new

    -- Add one var so we can ignore 0
    c_glucose_addVar solver

    -- Add enough vars for our clause set
    replicateM_ maxId (c_glucose_addVar solver)

    -- Add assumptions
    addAssumptions solver assumptions

    -- Add the clauses
    _ <- allM (addClause solver) clauses

    -- Get the result
    res <- c_solve solver
    m <- if res 
        then liftM Just $ getModel solver 
        else return Nothing

    cs <- if not res
        then liftM Just $ getConflicts solver
        else return Nothing

    -- Clean up
    c_glucose_delete solver

    return $ SatResult {
        satisfiable = res,
        model       = fmap (map fromIntegral) m,
        conflicts   = fmap (map fromIntegral) cs
        }

toDimacs :: Int -> Expression -> SolverT [SV.Vector CInt]
toDimacs mc e = do
    dimacs <- liftE $ getCachedStepDimacs mc e
    return (SV.singleton (fromIntegral (exprIndex e)) : dimacs)

minimiseCore :: Int -> Maybe [Assignment] -> Expression -> SolverT (Maybe [[Int]])
minimiseCore mc a e = do
    maxId       <- liftE $ getMaxId mc 
    clauses     <- toDimacs mc e
    assumptions <- liftE $ maybeM [] (mapM (assignmentToVar mc)) a
    let as      = map (\x -> if sign x == Pos then var x else -(var x)) assumptions

    doMinimiseCore maxId as clauses

doMinimiseCore :: Int -> [Int] -> [SV.Vector CInt] -> SolverT (Maybe [[Int]])
doMinimiseCore maxId assumptions clauses = do
    solver <- liftIO $ c_glucose_new

    liftIO $ replicateM_ (maxId+1) (c_glucose_addVar solver)

    liftIO $ addAssumptions solver assumptions

    _ <- liftIO $ allM (addClause solver) clauses

    res <- liftIO $ c_solve solver

    if res
    then do
        --SAT, there is no core to find
        liftIO $ c_glucose_delete solver
        return Nothing
    else do
        --UNSAT, try with no core
        cs <- liftIO $ getConflicts solver

        liftIO $ c_clearAssumptions solver
        noCore <- liftIO $ c_solve solver

        if noCore
        then do
            liftIO $ addAssumptions solver cs
            coresPtr    <- liftIO $ c_minimise_core solver
            coresPtrs   <- liftIO $ peekArray0 nullPtr coresPtr

            cores <- liftIO $ forM coresPtrs $ \p -> do
                core <- peekArray0 0 p
                free p
                return core

            liftIO $ free coresPtr
            liftIO $ c_glucose_delete solver

            return $ Just (map (map fromIntegral) cores)
        else do
            liftIO $ c_glucose_delete solver
            return (Just [])

addAssumptions :: Integral a => Ptr GlucoseSolver -> [a] -> IO ()
addAssumptions solver ass = do
    forM_ ass (c_addAssumption solver . fromIntegral)

addClause :: Ptr GlucoseSolver -> SV.Vector CInt -> IO Bool
addClause solver clause = do
    SV.unsafeWith clause (c_addClauseVector solver (fromIntegral (SV.length clause)))

getModel :: Ptr GlucoseSolver -> IO [CInt]
getModel solver = do
    p <- c_model solver
    m <- peekArray0 0 p
    free p
    return m

getConflicts :: Ptr GlucoseSolver -> IO [CInt]
getConflicts solver = do
    cs <- c_conflicts solver
    res <- peekArray0 0 cs
    free cs
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

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h addClauseVector"
    c_addClauseVector :: Ptr GlucoseSolver -> CInt -> Ptr CInt -> IO Bool

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h solve"
    c_solve :: Ptr GlucoseSolver -> IO Bool

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h minimise_core"
    c_minimise_core :: Ptr GlucoseSolver -> IO (Ptr (Ptr CInt))

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h model"
    c_model :: Ptr GlucoseSolver -> IO (Ptr CInt)

foreign import ccall unsafe "glucose_wrapper/glucose_wrapper.h conflicts"
    c_conflicts :: Ptr GlucoseSolver -> IO (Ptr CInt)
