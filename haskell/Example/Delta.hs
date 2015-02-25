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

sort :: [Int] -> Delta [Int]
sort xs = deltaFromList [ bubbleSort  xs,
                          singleSort  xs,
                          swapPair    xs,
                          identity,
                          nil
                        ]
    where
        nil = []
        identity = xs

        swapPair  []        = []
        swapPair  [x]       = [x]
        swapPair  (x:xx:xs) = (min x xx) : (max x xx) : xs

        singleSort []        = []
        singleSort xs        = (minimum xs) : (singleSort (filter (/= (minimum xs)) xs))

        bubbleSort []       = []
        bubbleSort xs       = let
                minVal  = minimum xs
                minVals = replicate (length (filter (== minVal) xs)) minVal
            in
                minVals ++ (bubbleSort (filter (/= (minimum xs)) xs))
