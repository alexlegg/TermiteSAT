{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.Interpolator (
      InterpolantResult(..)
    , interpolate
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad.State
import qualified Data.Vector.Storable as SV
import Expression.Expression
import SatSolver.Enode
import Synthesise.SolverT

data PeriploSolver

data InterpolantResult = InterpolantResult {
      success       :: Bool
    , interpolant   :: Maybe [[Assignment]]
} deriving (Show, Eq)

foreign import ccall safe "periplo_wrapper/periplo_wrapper.h interpolate"
    c_interpolate :: Ptr EnodeStruct -> Ptr EnodeStruct -> IO (Ptr (Ptr AssignmentStruct))

interpolate mc a b = do
    a'  <- lift $ foldExpression mc exprToEnodeExpr a
    b'  <- lift $ foldExpression mc exprToEnodeExpr b

    pa  <- liftIO $ enodeToStruct a'
    pb  <- liftIO $ enodeToStruct b'

    r   <- liftIO $ c_interpolate pa pb

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

    liftIO $ freeEnodeStruct pa
    liftIO $ freeEnodeStruct pb
    when (r /= nullPtr) $ liftIO $ freeCubes r

    return $ InterpolantResult {
        success     = succ,
        interpolant = i
    }

exprToEnodeExpr :: Int -> Expr -> [(Sign, EnodeExpr)] -> EnodeExpr
exprToEnodeExpr i (ELit _) []       = EnodeExpr EnodeVar (Just i) []
exprToEnodeExpr i (ENot _) cs       = EnodeExpr EnodeNot Nothing (expandNots cs)
exprToEnodeExpr i (EConjunct _) cs  = EnodeExpr EnodeAnd Nothing (expandNots cs)
exprToEnodeExpr i (EDisjunct _) cs  = EnodeExpr EnodeOr Nothing (expandNots cs)
exprToEnodeExpr i (ETrue) _         = EnodeExpr EnodeTrue Nothing []
exprToEnodeExpr i (EFalse) _        = EnodeExpr EnodeFalse Nothing []

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
    
