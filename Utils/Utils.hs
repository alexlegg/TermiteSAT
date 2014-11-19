module Utils.Utils (
      zipMaybe1
    , zipMaybe2
    , mapFst
    , mapSnd
    , concatMapM
    , mapMUntilJust
    , liftMSnd
    , liftMFst
    , everyOdd
    , everyEven
    , adjust
    , lookupIndex
    , interMap
    ) where

import Data.Maybe
import Data.List
import Control.Monad

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

concatMapM :: Monad m => (a -> m [b]) -> [a] -> m [b]
concatMapM f xs = (liftM concat) (mapM f xs)

mapMUntilJust :: (Monad m) => (a -> m (Maybe b)) -> [a] -> m (Maybe b)
mapMUntilJust _ []      = return Nothing
mapMUntilJust f (a:as)  = do
    b <- f a
    if isJust b
    then return b
    else mapMUntilJust f as

liftMFst :: Monad m => m a -> b -> m (a, b)
liftMFst a b = do
    a' <- a
    return (a', b)

liftMSnd :: Monad m => a -> m b -> m (a, b)
liftMSnd a b = do
    b' <- b
    return (a, b')

everyOdd :: [a] -> [a]
everyOdd []         = []
everyOdd (a:[])     = [a]
everyOdd (a:b:as)   = a : everyOdd as

everyEven :: [a] -> [a]
everyEven []         = []
everyEven (a:[])     = []
everyEven (a:b:as)   = b : everyEven as

adjust :: (a -> a) -> Int -> [a] -> [a]
adjust f k []   = []
adjust f k (m:ms)
    | k == 0    = (f m) : ms
    | otherwise = m : (adjust f (k-1) ms)

lookupIndex :: Eq a => a -> [(a, b)] -> Maybe Int
lookupIndex x = findIndex (\(a, b) -> a == x)

interMap :: [a] -> (b -> [a]) -> [b] -> [a]
interMap x f bs = intercalate x (map f bs)
