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

data PeriploSolver

data InterpolantResult = InterpolantResult {
      success       :: Bool
    , interpolant   :: [[Int]]
} deriving (Show, Eq)

foreign import ccall safe "periplo_wrapper/periplo_wrapper.h interpolate"
    c_interpolate :: Ptr EnodeStruct -> Ptr EnodeStruct -> IO CInt

interpolate mc a b = do
    a'  <- lift $ foldExpression mc exprToEnodeExpr a
    b'  <- lift $ foldExpression mc exprToEnodeExpr b

    pa  <- liftIO $ enodeToStruct a'
    pb  <- liftIO $ enodeToStruct b'

    r   <- liftIO $ c_interpolate pa pb

    liftIO $ freeEnodeStruct pa
    liftIO $ freeEnodeStruct pb

    liftIO $ putStrLn ("Interpolation result: " ++ (show r))

    return $ InterpolantResult {
        success = False,
        interpolant = []
    }

exprToEnodeExpr :: Int -> Expr -> [(Sign, EnodeExpr)] -> EnodeExpr
exprToEnodeExpr i (ELit _) []       = EnodeExpr EnodeVar (Just i) []
exprToEnodeExpr i (ENot _) cs       = EnodeExpr EnodeNot Nothing (expandNots cs)
exprToEnodeExpr i (EConjunct _) cs  = EnodeExpr EnodeAnd Nothing (expandNots cs)
exprToEnodeExpr i (EDisjunct _) cs  = EnodeExpr EnodeOr Nothing (expandNots cs)

expandNots []               = []
expandNots ((Pos, x):xs)    = x : expandNots xs
expandNots ((Neg, x):xs)    = EnodeExpr EnodeNot Nothing [x] : expandNots xs
    
