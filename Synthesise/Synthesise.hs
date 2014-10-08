{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
    synthesise
    ) where

import Expression.Parse
import Expression.Compile
import Expression.Expression
import Debug.Trace
import Control.Monad.State
import qualified Data.Map as Map

initState = ExprManager { maxIndex = 3, exprMap = Map.empty }

synthesise :: ParsedSpec -> Either String Bool
synthesise spec = do
    let ParsedSpec{..} = spec

    (c, m) <- runStateT (compile init) initState 

    trace (show c) $ Right True
