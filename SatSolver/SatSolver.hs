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

satSolve :: Maybe [Assignment] -> Expression -> SolverT SatResult
satSolve a e = do
    maxId       <- liftE $ getMaxId
    clauses     <- toDimacsS e
    assumptions <- liftE $ maybeM [] (mapM assignmentToVar) a
    let as      = map (\a -> if sign a == Pos then var a else -(var a)) assumptions

    liftIO $ callSolver maxId as clauses

callSolver :: Int -> [Int] -> [SV.Vector CInt] -> IO SatResult
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

toDimacsS e = do
    ds      <- (liftM ISet.toList) $ liftE $ getDependencies (exprIndex e)
    es      <- (liftM catMaybes) $ liftE $ mapM lookupExpression ds
    let vs  = concatMap makeVector es
    return (SV.singleton (fromIntegral (exprIndex e)) : vs)

makeVector :: Expression -> [(SV.Vector CInt)]
makeVector e = case exprType e of
    (ETrue)         -> [(SV.singleton i)]
    (EFalse)        -> [(SV.singleton (-i))]
    (ENot _)        -> [ SV.fromList [-i, -(lit x)]
                       , SV.fromList [i, (lit x)]]
    (ELit _)        -> []
    (EEquals _ _)   -> [ SV.fromList [-i, -(lit a), (lit b)]
                       , SV.fromList [-i, (lit a), -(lit b)]
                       , SV.fromList [i, (lit a), (lit b)]
                       , SV.fromList [i, -(lit a), -(lit b)]]
    (EConjunct _)   -> SV.fromList (i : (map (negate . lit) cs)) : (map (\c -> SV.fromList [-i, (lit c)]) cs)
    (EDisjunct _)   -> SV.fromList (-i : map lit cs) : (map (\c -> SV.fromList [i, -(lit c)]) cs)
    where
        i       = fromIntegral $ exprIndex e
        cs      = exprChildren (exprType e)
        (x:_)   = cs
        (a:b:_) = exprChildren (exprType e)

lit (Var Pos v) = fromIntegral v
lit (Var Neg v) = fromIntegral (-v)

makeDimacs :: Expression -> [[Int]]
makeDimacs e = case exprType e of
    (ETrue)         -> [[i]]
    (EFalse)        -> [[-i]]
    (ENot _)        -> [[-i, -(lit x)], [i, (lit x)]]
    (ELit _)        -> []
    (EEquals _ _)   -> [[-i, -(lit a), (lit b)], [-i, (lit a), -(lit b)],
                        [i, (lit a), (lit b)], [i, -(lit a), -(lit b)]]
    (EConjunct _)   -> (i : (map (negate . lit) cs)) : (map (\c -> [-i, (lit c)]) cs)
    (EDisjunct _)   -> (-i : map lit cs) : (map (\c -> [i, -(lit c)]) cs)
    where
        i       = exprIndex e
        cs      = exprChildren (exprType e)
        (x:_)   = cs
        (a:b:_) = exprChildren (exprType e)

minimiseCore :: Int -> [Int] -> [[Int]] -> SolverT [Int]
minimiseCore max assumptions clauses = do
    liftIO $ doMinimiseCore max assumptions clauses

doMinimiseCore :: Int -> [Int] -> [[Int]] -> IO [Int]
doMinimiseCore max assumptions clauses = do
    solver <- c_glucose_new

    replicateM_ (max+1) (c_glucose_addVar solver)

    addAssumptions solver assumptions

    allM (addClause solver) clauses

    core_ptr <- c_minimise_core solver
    core <- peekArray0 0 core_ptr
    free core_ptr

    c_glucose_delete solver

    return $ map fromIntegral core

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
