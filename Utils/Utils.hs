module Utils.Utils (
      zipMaybe1
    , zipMaybe2
    , mapFst
    , mapSnd
    ) where

import Data.Maybe

zipMaybe1 :: [Maybe a] -> [b] -> [(a, b)]
zipMaybe1 as bs = mapMaybe f (zip as bs)
    where
    f (a, b) = do
        a' <- a
        return (a', b)

zipMaybe2 :: [a] -> [Maybe b] -> [(a, b)]
zipMaybe2 as bs = mapMaybe f (zip as bs)
    where
    f (a, b) = do
        b' <- b
        return (a, b')

mapFst :: (a -> b) -> (a, c) -> (b, c)
mapFst f (x,y) = (f x,y)

mapSnd :: (a -> b) -> (c, a) -> (c, b)
mapSnd f (x,y) = (x,f y)
