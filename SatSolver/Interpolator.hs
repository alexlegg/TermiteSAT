{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.Interpolator (
      InterpolantResult(..)
    , interpolate
    , timeInInterpolate
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad.State
import qualified Data.Vector.Storable as SV
import Expression.Expression hiding (exprChildren)
import SatSolver.Enode
import Synthesise.SolverT
import System.TimeIt
import Data.IORef
import Data.List
import System.IO.Unsafe
import System.CPUTime

data PeriploSolver
data Enode

data InterpolantResult = InterpolantResult {
      success       :: Bool
    , interpolant   :: Maybe [[Assignment]]
} deriving (Show, Eq)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h newSolver"
    c_newSolver :: IO (Ptr PeriploSolver)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h deleteSolver"
    c_deleteSolver :: (Ptr PeriploSolver) -> IO ()

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h interpolate"
    c_interpolate :: Ptr PeriploSolver -> Ptr CInt -> CInt -> Ptr Enode -> Ptr Enode -> IO (Ptr (Ptr AssignmentStruct))

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h mkConjunct"
    c_mkConjunct :: Ptr PeriploSolver -> CInt -> Ptr (Ptr Enode) -> IO (Ptr Enode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h mkDisjunct"
    c_mkDisjunct :: Ptr PeriploSolver -> CInt -> Ptr (Ptr Enode) -> IO (Ptr Enode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h mkNegation"
    c_mkNegation :: Ptr PeriploSolver -> Ptr Enode -> IO (Ptr Enode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h mkVariable"
    c_mkVariable :: Ptr PeriploSolver -> CInt -> IO (Ptr Enode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h mkTrue"
    c_mkTrue :: Ptr PeriploSolver -> IO (Ptr Enode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h mkFalse"
    c_mkFalse :: Ptr PeriploSolver -> IO (Ptr Enode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h checkFml"
    c_checkFml :: Ptr PeriploSolver -> Ptr Enode -> IO CInt


totalTime :: IORef Double
{-# NOINLINE totalTime #-}
totalTime = unsafePerformIO (newIORef 0)

enodeATime :: IORef Double
{-# NOINLINE enodeATime #-}
enodeATime = unsafePerformIO (newIORef 0)

enodeBTime :: IORef Double
{-# NOINLINE enodeBTime #-}
enodeBTime = unsafePerformIO (newIORef 0)

timeInInterpolate :: IO (Double, Double, Double)
timeInInterpolate = do
    t <- readIORef totalTime
    tA <- readIORef enodeATime
    tB <- readIORef enodeBTime
    writeIORef totalTime 0
    writeIORef enodeATime 0
    writeIORef enodeBTime 0
    return (t, tA, tB)

interpolate :: Int -> [Int] -> Expression -> Expression -> SolverT InterpolantResult
interpolate mc project a b = do
    t1  <- liftIO $ getCPUTime
    r   <- interpolate' mc project a b
    t2  <- liftIO $ getCPUTime
    let t = fromIntegral (t2-t1) * 1e-12 :: Double
    liftIO $ modifyIORef totalTime (\total -> t + total)
---    liftIO $ putStrLn $ "int " ++ (show ((fromInteger $ round $ (t * 10)) / 10.0))
    return r

interpolate' mc project a b = do
    ctx <- liftIO $ c_newSolver

    tA1     <- liftIO $ getCPUTime
    enodeA  <- lift $ foldExpressionIO mc (exprToEnode ctx) a
    rA      <- liftIO $ c_checkFml ctx enodeA
    tA2     <- liftIO $ getCPUTime
    let tA = fromIntegral (tA2-tA1) * 1e-12 :: Double
    liftIO $ modifyIORef enodeATime (\total -> tA + total)

---    liftIO $ putStrLn $ "intA " ++ (show ((fromInteger $ round $ (tA * 10)) / 10.0))

    if (rA == 0)
    then do
        liftIO $ c_deleteSolver ctx
        return $ InterpolantResult {
            success = False,
            interpolant = Nothing
            }
    else do
        tB1     <- liftIO $ getCPUTime
        enodeB  <- lift $ foldExpressionIO mc (exprToEnode ctx) b
        rB      <- liftIO $ c_checkFml ctx enodeB
        tB2     <- liftIO $ getCPUTime
        let tB = fromIntegral (tB2-tB1) * 1e-12 :: Double
        liftIO $ modifyIORef enodeBTime (\total -> tB + total)

---        liftIO $ putStrLn $ "intB " ++ (show ((fromInteger $ round $ (tB * 10)) / 10.0))

        if (rB == 1)
        then do
            liftIO $ c_deleteSolver ctx
            return $ InterpolantResult {
                success = False,
                interpolant = Nothing
                }
        else do
            let pv = SV.fromList (map fromIntegral project) :: SV.Vector CInt
            r <- liftIO $ SV.unsafeWith pv (\ps -> c_interpolate ctx ps (fromIntegral (SV.length pv)) enodeA enodeB)
            liftIO $ c_deleteSolver ctx

            let succ = (r /= nullPtr)
            i   <- if succ 
                then do 
                    assignments <- liftIO $ cubesToAssignments r
                    liftM Just $ forM assignments $ \vs -> do
                        let (ss, vars)  = unzip vs
                        es              <- liftE $ mapM (lookupExpression mc) vars
                        let vars'       = map (\(Just v) -> (\(ELit var) -> var) (exprType v)) es
                        return $ zipWith Assignment ss vars'
                else return Nothing

            when (r /= nullPtr) $ liftIO $ freeCubes r

            return $ InterpolantResult {
                success     = succ,
                interpolant = i
            }

exprToEnode :: Ptr PeriploSolver -> Int -> Expr -> [(Sign, Ptr Enode)] -> IO (Ptr Enode)
exprToEnode ctx i (ELit _) []       = c_mkVariable ctx (fromIntegral i)
exprToEnode ctx i (ENot _) (c:[])   = c_mkNegation ctx (snd c)
exprToEnode ctx i (EConjunct _) cs  = do
    let (ps, ns) = partition ((==) Pos . fst) cs
    ns' <- mapM (c_mkNegation ctx) (map snd ns)
    let lits = map snd ps ++ ns'
    SV.unsafeWith (SV.fromList lits) (c_mkConjunct ctx (fromIntegral (length lits)))
exprToEnode ctx i (EDisjunct _) cs  = do
    let (ps, ns) = partition ((==) Pos . fst) cs
    ns' <- mapM (c_mkNegation ctx) (map snd ns)
    let lits = map snd ps ++ ns'
    SV.unsafeWith (SV.fromList lits) (c_mkDisjunct ctx (fromIntegral (length lits)))
exprToEnode ctx i (ETrue) _         = c_mkTrue ctx
exprToEnode ctx i (EFalse) _        = c_mkFalse ctx
