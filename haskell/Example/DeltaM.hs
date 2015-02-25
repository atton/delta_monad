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
-- usage   : runWriter $ checkOut 0 $ numberCountM 30  -- run specific version
--         : dmap runWriter $ numberCountM 30          -- run all version

generatorM :: Int -> DeltaWithLog [Int]
generatorM x = let intList = [1..x] in
                             DeltaM $ deltaFromList $ fmap returnW $ replicate 2 intList

numberFilterM :: [Int] -> DeltaWithLog [Int]
numberFilterM xs = let primeList = filter isPrime xs
                       evenList  = filter even xs    in
                      DeltaM $ deltaFromList $ fmap returnW [primeList, evenList]


countM :: [Int] -> DeltaWithLog Int
countM xs = let numberCount = length xs in
                DeltaM $ deltaFromList $ fmap returnW $ replicate 2 numberCount

numberCountM :: Int -> DeltaWithLog Int
numberCountM x = generatorM x >>= numberFilterM >>= countM


-- example : sort

sort :: [Int] -> DeltaWithLog [Int]
sort xs = DeltaM $ deltaFromList [ --bubbleSort xs,
                          singleSort xs,
                          returnW $ swapPair xs,
                          identity,
                          nil
                        ]
    where
        nil = returnW []

        identity = returnW xs

        swapPair  []        = []
        swapPair  [x]       = [x]
        swapPair  (x:xx:xs) = (min x xx) : (max x xx) : xs

        singleSort []        = returnW []
        singleSort xs        = do
                tell [show xs]
                res <- do
                    remanVals <- singleSort $ filter (/= (minimum xs)) xs
                    return $ (minimum xs) : remanVals
                tell [ show res ]
                return res

        bubbleSort []       = returnW []
        bubbleSort xs       = let
                minVal  = minimum xs
                minVals = replicate (length (filter (== minVal) xs)) minVal
            in
                do
                    tell [show xs]
                    res <- do
                            remainVals <- bubbleSort $ filter (/= minVal) xs
                            return $ minVals ++ remainVals
                    tell [show res]
                    return res
