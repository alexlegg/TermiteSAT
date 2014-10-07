{-# LANGUAGE RecordWildCards #-}
module Synthesise.Synthesise (
    synthesise
    ) where

import Expression.Parse
import Expression.Compile

synthesise spec = do
    let ParsedSpec{..} = spec

    let c = compile init

    Right True
