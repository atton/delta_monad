module Example.Delta where

import Data.Numbers.Primes
import Delta

-- samples

generator :: Int -> Delta [Int]
generator x = let intList = [1..x] in
                  return intList

primeFilter :: [Int] -> Delta [Int]
primeFilter xs = let primeList    = filter isPrime xs
                     refactorList = filter even xs    in
                 deltaFromList [ primeList, refactorList]

count :: [Int] -> Delta Int
count xs = let primeCount = length xs in
           return primeCount

primeCount :: Int -> Delta Int
primeCount x = generator x >>= primeFilter >>= count

bubbleSort :: [Int] -> Delta [Int]
bubbleSort [] = return []
bubbleSort xs = bubbleSort remainValue >>= (\xs -> deltaFromList [ (sortedValueL : xs),
                                                                   (sortedValueR ++ xs)] )
    where
        maximumValue = maximum xs
        sortedValueL = maximumValue
        sortedValueR = replicate (length $ filter (== maximumValue) xs) maximumValue
        remainValue  = filter (/= maximumValue) xs




