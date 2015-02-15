module Example.Delta where

import Data.Numbers.Primes
import Delta

-- examples

generator :: Int -> Delta [Int]
generator x = let intList = [1..x] in
                  return intList

numberFilter :: [Int] -> Delta [Int]
numberFilter xs = let primeList = filter isPrime xs
                      evenList  = filter even xs    in
                  Delta evenList (Mono primeList)

count :: [Int] -> Delta Int
count xs = let primeCount = length xs in
           return primeCount

numberCount :: Int -> Delta Int
numberCount x = generator x >>= numberFilter >>= count
