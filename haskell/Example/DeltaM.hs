module Example.DeltaM where

import Control.Monad.Writer
import Data.Numbers.Primes -- $ cabal install primes

import Delta
import DeltaM


-- DeltaM examples

-- DeltaM example utils
type DeltaLog     = Writer [String]
type DeltaWithLog = DeltaM DeltaLog

returnW :: (Show a) => a -> DeltaLog a
returnW x = do tell $ [show x]
               return x

dmap :: (m a -> b) -> DeltaM m a -> Delta b
dmap f (DeltaM d) = fmap f d

deltaWithLogFromList :: (Show a) => [a] -> DeltaWithLog a
deltaWithLogFromList xs = DeltaM $ deltaFromList $ fmap returnW xs


-- example : prime filter
-- usage   : runWriter $ checkOut 0 $ primeCountM 30  -- run specific version
--         : dmap runWriter $ primeCountM 30          -- run all version

generatorM :: Int -> DeltaWithLog [Int]
generatorM x = let intList = [1..x] in
                             DeltaM $ deltaFromList $ fmap returnW $ replicate 2 intList

primeFilterM :: [Int] -> DeltaWithLog [Int]
primeFilterM xs = let primeList    = filter isPrime xs
                      refactorList = filter even xs    in
                      DeltaM $ deltaFromList $ fmap returnW [primeList, refactorList]


countM :: [Int] -> DeltaWithLog Int
countM xs = let primeCount = length xs in
                DeltaM $ deltaFromList $ fmap returnW $ replicate 2 primeCount

primeCountM :: Int -> DeltaWithLog Int
primeCountM x = generatorM x >>= primeFilterM >>= countM
