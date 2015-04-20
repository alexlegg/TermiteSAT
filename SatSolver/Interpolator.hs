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
import Expression.Expression
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

timeInInterpolate :: IO Double
timeInInterpolate = do
    t <- readIORef totalTime
    writeIORef totalTime 0
    return t

interpolate :: Int -> [Int] -> Expression -> Expression -> SolverT InterpolantResult
interpolate mc project a b = do
    t1  <- liftIO $ getCPUTime
    r   <- interpolate' mc project a b
    t2  <- liftIO $ getCPUTime
    let t = fromIntegral (t2-t1) * 1e-12 :: Double
    liftIO $ modifyIORef totalTime (\total -> t + total)
    return r

interpolate' mc project a b = do
    ctx <- liftIO $ c_newSolver

    enodeA  <- lift $ foldExpressionIO mc (exprToEnode ctx) a
    rA      <- liftIO $ c_checkFml ctx enodeA

    if (rA == 0)
    then do
        liftIO $ c_deleteSolver ctx
        return $ InterpolantResult {
            success = False,
            interpolant = Nothing
            }
    else do
        enodeB  <- lift $ foldExpressionIO mc (exprToEnode ctx) b
        rB      <- liftIO $ c_checkFml ctx enodeB

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


exprToEnodeExpr :: Int -> Expr -> [(Sign, EnodeExpr)] -> IO EnodeExpr
exprToEnodeExpr i (ELit _) []       = return $ EnodeExpr EnodeVar (Just i) []
exprToEnodeExpr i (ENot _) cs       = return $ EnodeExpr EnodeNot Nothing (expandNots cs)
exprToEnodeExpr i (EConjunct _) cs  = return $ EnodeExpr EnodeAnd Nothing (expandNots cs)
exprToEnodeExpr i (EDisjunct _) cs  = return $ EnodeExpr EnodeOr Nothing (expandNots cs)
exprToEnodeExpr i (ETrue) _         = return $ EnodeExpr EnodeTrue Nothing []
exprToEnodeExpr i (EFalse) _        = return $ EnodeExpr EnodeFalse Nothing []

expandNots []               = []
expandNots ((Pos, x):xs)    = x : expandNots xs
expandNots ((Neg, x):xs)    = EnodeExpr EnodeNot Nothing [x] : expandNots xs
    
enodeExprToExpr :: MonadIO m => Int -> EnodeExpr -> ExpressionT m Expression
enodeExprToExpr mc e = do
    case (exprEType e) of
        EnodeInvalid    -> error "Invalid enode"
        EnodeVar        -> do
            let (Just i) = exprVarId e
            Just e <- lookupExpression mc i
            return e
        EnodeAnd        -> do
            cs <- mapM (enodeExprToExpr mc) (exprChildren e)
            conjunctC mc cs
        EnodeOr         -> do
            cs <- mapM (enodeExprToExpr mc) (exprChildren e)
            disjunctC mc cs
        EnodeNot        -> do
            c <- enodeExprToExpr mc (head (exprChildren e))
            negationC mc c
    
