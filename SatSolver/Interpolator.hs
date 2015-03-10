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

data ENodeType = ENodeVar | ENodeAnd | ENodeOr | ENodeNot deriving (Eq, Show, Enum)

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

exprToPeriplo s _ ETrue _ = liftIO $ c_periplo_enodeTrue s

exprToPeriplo s _ EFalse _ = liftIO $ c_periplo_enodeFalse s

exprToPeriplo s i (ELit _) _ = do
    e <- liftIO $ c_periplo_enodeVar s (fromIntegral i)
    return e

exprToPeriplo s _ (ENot _) ((Pos,v):[]) = do
    liftIO $ c_periplo_enodeNot s v

exprToPeriplo s _ (EEquals _ _) ((s1,v1):(s2,v2):[]) = error $ "Not implemented"

exprToPeriplo s _ (EConjunct _) vs = do
    vs' <- forM vs $ \(sign, v) -> do
        if sign == Pos 
            then return v
            else do
                liftIO $ c_periplo_enodeNot s v

    let vec = SV.fromList vs'
    liftIO $ SV.unsafeWith vec (c_periplo_enodeAnd s (fromIntegral (length vs')))

exprToPeriplo s _ (EDisjunct _) vs = do
    vs' <- forM vs $ \(sign, v) -> do
        if sign == Pos 
            then return v
            else liftIO $ c_periplo_enodeNot s v

    let vec = SV.fromList vs'
    liftIO $ SV.unsafeWith vec (c_periplo_enodeOr s (fromIntegral (length vs')))

periploToExpr s e = do
    typ <- liftIO $ c_periplo_enodeType s e

    case toEnum (fromIntegral typ) of
        ENodeVar    -> do
            v <- liftIO $ c_periplo_enodeVarId s e
            liftIO $ putStrLn (show v)
            return ()
        ENodeAnd    -> return ()
        ENodeOr     -> return ()
        ENodeNot    -> return ()

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_new"
    c_periplo_new :: IO (Ptr PeriploSolver)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h periplo_delete"
    c_periplo_delete :: Ptr PeriploSolver -> IO ()

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeTrue"
    c_periplo_enodeTrue :: Ptr PeriploSolver -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeFalse"
    c_periplo_enodeFalse :: Ptr PeriploSolver -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeNot"
    c_periplo_enodeNot :: Ptr PeriploSolver -> Ptr ENode -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeAnd"
    c_periplo_enodeAnd :: Ptr PeriploSolver -> CInt -> Ptr (Ptr ENode) -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeOr"
    c_periplo_enodeOr :: Ptr PeriploSolver -> CInt -> Ptr (Ptr ENode) -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrappher.h enodeVar"
    c_periplo_enodeVar :: Ptr PeriploSolver -> CInt -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h interpolate"
    c_periplo_interpolate :: Ptr PeriploSolver -> Ptr ENode -> Ptr ENode -> IO Bool

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h interpolant"
    c_periplo_interpolant :: Ptr PeriploSolver -> IO (Ptr ENode)

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h enodeType"
    c_periplo_enodeType :: Ptr PeriploSolver -> Ptr ENode -> IO CInt

foreign import ccall unsafe "periplo_wrapper/periplo_wrapper.h enodeVarId"
    c_periplo_enodeVarId :: Ptr PeriploSolver -> Ptr ENode -> IO CInt
