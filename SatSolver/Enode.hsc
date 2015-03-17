module SatSolver.Enode (
      EnodeExpr(..)
    , EnodeType(..)
    , EnodeStruct
    , enodeToStruct
    , structToEnode
    , freeEnodeStruct
    ) where

import Foreign
import Foreign.C
import Data.Maybe

#include "periplo_wrapper.h"

data EnodeType =
      EnodeInvalid
    | EnodeVar
    | EnodeAnd
    | EnodeOr
    | EnodeNot
    deriving (Show, Eq, Enum)

data EnodeExpr = EnodeExpr
    { exprEType     :: EnodeType
    , exprVarId     :: Maybe Int
    , exprChildren  :: [EnodeExpr]
    } deriving (Show, Eq)

data EnodeStruct = EnodeStruct
    { enodeType     :: !CInt
    , enodeVarId    :: !CInt
    , enodeChildren :: !(Ptr (Ptr EnodeStruct))
    , enodeArity    :: !CInt
    } deriving (Show)

#let alignment t = "%lu", (unsigned long)offsetof(struct {char x__; t (y__); }, y__)

instance Storable EnodeStruct where
    sizeOf _        = #{size EnodeExpr}

    alignment _     = #{alignment EnodeExpr}

    peek ptr        = do
        typ         <- #{peek EnodeExpr, enodeType} ptr
        varId       <- #{peek EnodeExpr, enodeVarId} ptr
        children    <- #{peek EnodeExpr, enodeChildren} ptr
        arity       <- #{peek EnodeExpr, enodeArity} ptr
        return (EnodeStruct typ varId children arity)

    poke ptr (EnodeStruct typ varId children arity) = do
        #{poke EnodeExpr, enodeType} ptr typ
        #{poke EnodeExpr, enodeVarId} ptr varId
        #{poke EnodeExpr, enodeChildren} ptr children
        #{poke EnodeExpr, enodeArity} ptr arity

enodeToStruct :: EnodeExpr -> IO (Ptr EnodeStruct)
enodeToStruct e = case (exprEType e) of
    EnodeInvalid    -> error "Invalid Enode"

    EnodeVar        -> do
        let struct = EnodeStruct {
              enodeType     = fromIntegral (fromEnum (exprEType e))
            , enodeVarId    = fromIntegral (fromJust (exprVarId e))
            , enodeChildren = nullPtr
            , enodeArity    = 0 }
        p <- malloc
        poke p struct
        return p

    _               -> do
        cs <- mapM enodeToStruct (exprChildren e)
        cp <- newArray cs

        let struct = EnodeStruct {
              enodeType     = fromIntegral (fromEnum (exprEType e))
            , enodeVarId    = 0
            , enodeChildren = cp
            , enodeArity    = fromIntegral (length (exprChildren e)) }

        p <- malloc
        poke p struct
        return p

freeEnodeStruct :: Ptr EnodeStruct -> IO ()
freeEnodeStruct p = do
    s <- peek p
    case (toEnum (fromIntegral (enodeType s))) of
        EnodeInvalid    -> error "Invalid enode"

        EnodeVar        -> do
            free p

        _               -> do
            cs <- peekArray (fromIntegral (enodeArity s)) (enodeChildren s)
            mapM freeEnodeStruct cs
            free (enodeChildren s)
            free p

structToEnode :: Ptr EnodeStruct -> IO EnodeExpr
structToEnode p = do
    struct <- peek p

    let varId = case (toEnum (fromIntegral (enodeType struct))) of
                EnodeVar    -> Just (fromIntegral (enodeVarId struct))
                _           -> Nothing

    cs <- peekArray (fromIntegral (enodeArity struct)) (enodeChildren struct)
    children <- mapM structToEnode cs

    return $ EnodeExpr {
          exprEType      = toEnum (fromIntegral (enodeType struct))
        , exprVarId     = varId
        , exprChildren  = children
        }
