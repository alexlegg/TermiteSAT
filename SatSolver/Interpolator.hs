{-# LANGUAGE ForeignFunctionInterface #-}
module SatSolver.Interpolator (
      InterpolantResult(..)
    , InterpolatorST(..)
    , InterpolantState(..)
    , interpolate
    ) where

import Foreign
import Foreign.C.Types
import Control.Monad.State
import qualified Data.Vector.Storable as SV
import Expression.Expression

type InterpolatorST m = StateT InterpolantState m

data PeriploSolver

data ENode

type InterpolantState = Maybe (Ptr PeriploSolver)

data InterpolantResult = InterpolantResult {
      success       :: Bool
    , interpolant   :: [[Int]]
} deriving (Show, Eq)

interpolate mc a b = do
    solver <- liftIO $ c_periplo_new

    pa <- lift $ foldExpressionM mc (exprToPeriplo solver) a
    pb <- lift $ foldExpressionM mc (exprToPeriplo solver) b

    r <- liftIO $ c_periplo_interpolate solver pa pb
    when r $ do
        enode <- liftIO $ c_periplo_interpolant solver
        return ()

    liftIO $ c_periplo_delete solver 

    return $ InterpolantResult {
        success = False,
        interpolant = []
    }

exprToPeriplo :: MonadIO m => Ptr PeriploSolver -> Int -> Expr -> [(Sign, Ptr ENode)] -> m (Ptr ENode)

exprToPeriplo s i ETrue cs = liftIO $ c_periplo_enodeTrue s

exprToPeriplo s i EFalse cs = liftIO $ c_periplo_enodeFalse s

exprToPeriplo s i (ELit v) cs = do
    liftIO $ c_periplo_enodeFalse s

addClauseA solver clause = do
    SV.unsafeWith clause (c_periplo_addClause solver True (fromIntegral (SV.length clause)))

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_new"
    c_periplo_new :: IO (Ptr PeriploSolver)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_delete"
    c_periplo_delete :: Ptr PeriploSolver -> IO ()

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_addClause"
    c_periplo_addClause :: Ptr PeriploSolver -> Bool -> CInt -> Ptr CInt -> IO ()

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeTrue"
    c_periplo_enodeTrue :: Ptr PeriploSolver -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeFalse"
    c_periplo_enodeFalse :: Ptr PeriploSolver -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeNot"
    c_periplo_enodeNot :: Ptr PeriploSolver -> Ptr ENode -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeAnd"
    c_periplo_enodeAnd :: Ptr PeriploSolver -> Ptr ENode -> IO (Ptr (Ptr ENode))

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeOr"
    c_periplo_enodeOr :: Ptr PeriploSolver -> Ptr ENode -> IO (Ptr (Ptr ENode))

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeVar"
    c_periplo_enodeVar :: Ptr PeriploSolver -> CInt -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h interpolate"
    c_periplo_interpolate :: Ptr PeriploSolver -> Ptr ENode -> Ptr ENode -> IO Bool

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h interpolant"
    c_periplo_interpolant :: Ptr PeriploSolver -> IO (Ptr ENode)
