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
    , update
    , lookupIndex
    , interMap
    , ungroupZip
    , paddedZip
    , fst3 , snd3 , thd3
    , fst4 , snd4 , thd4, fth4
    , unzipM
    , maybeM
    , zipWith3M
    , floor2
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

update :: a -> Int -> [a] -> [a]
update a k []   = []
update a k (b:bs)
    | k == 0    = a : bs
    | otherwise = b : (update a (k-1) bs)

lookupIndex :: Eq a => a -> [(a, b)] -> Maybe Int
lookupIndex x = findIndex (\(a, b) -> a == x)

interMap :: [a] -> (b -> [a]) -> [b] -> [a]
interMap x f bs = intercalate x (map f bs)

ungroupZip :: [(a, [b])] -> [(a, b)]
ungroupZip = concatMap (\(a, bs) -> map (\b -> (a, b)) bs)

paddedZip :: [a] -> [b] -> [(a, Maybe b)]
paddedZip [] _          = []
paddedZip (a:as) []     = (a, Nothing) : paddedZip as []
paddedZip (a:as) (b:bs) = (a, Just b) : paddedZip as bs

fst3 :: (a, b, c) -> a
fst3 (a, b, c) = a

snd3 :: (a, b, c) -> b
snd3 (a, b, c) = b

thd3 :: (a, b, c) -> c
thd3 (a, b, c) = c

fst4 :: (a, b, c, d) -> a
fst4 (a, b, c, d) = a

snd4 :: (a, b, c, d) -> b
snd4 (a, b, c, d) = b

thd4 :: (a, b, c, d) -> c
thd4 (a, b, c, d) = c

fth4 :: (a, b, c, d) -> d
fth4 (a, b, c, d) = d

unzipM :: Monad m => m [(a, b)] -> m ([a], [b])
unzipM = liftM unzip

maybeM :: Monad m => b -> (a -> m b) -> Maybe a -> m b
maybeM _ f (Just a) = f a
maybeM b f Nothing  = return b

floor2 :: Int -> Int
floor2 x = (quot x 2) * 2

zipWith3M :: Monad m => (a -> b -> c -> m d) -> [a] -> [b] -> [c] -> m [d]
zipWith3M f as bs cs = sequence (zipWith3 f as bs cs)
