import Control.Applicative
import Data.Numbers.Primes -- $ cabal install primes

data Delta a = Delta [String] a [String] a

instance (Show a) => Show (Delta a) where
    show (Delta lx x ly y) = values ++ logs
        where
            values        = "Delta {" ++ (show x) ++ "|" ++ (show y) ++ "}\n"
            logs          = concat . reverse $ zipWith formatter lx ly
            formatter x y = "      {" ++ x ++ (separator x y) ++ y ++ "}\n"
            separator x y = if (max (length x) (length y)) > 50 then "|\n       " else "|"

value :: (Delta a) -> a
value (Delta _ x _ _) = x

deltaLeft :: (Delta a) -> a
deltaLeft (Delta _ x _ _) = x

deltaRight :: (Delta a) -> a
deltaRight (Delta _ _ _ y) = y

instance (Eq a) => Eq (Delta a) where
    s == ss = (value s) == (value ss)

instance Functor Delta where
    fmap f (Delta xs x ys y) = Delta xs (f x) ys (f y)

-- not proof
fmapS :: (Show a) => (a -> b) -> Delta a -> Delta b
fmapS f (Delta lx x ly y) = Delta (lx ++ [(show x)]) (f x) (ly ++ [(show y)]) (f y)

-- not proof
fmapSS :: (Show a) => (a -> b) -> (a -> b) -> Delta a -> Delta b
fmapSS f g (Delta lx x ly y) = Delta (lx ++ [(show x)]) (f x) (ly ++ [(show y)]) (g y)

instance Applicative Delta where
    pure f                                      = Delta [] f [] f
    (Delta lf f lg g) <*> (Delta lx x ly y) = Delta (lf ++ lx) (f x) (lg ++ ly) (g y)

mu :: Delta (Delta a) -> Delta a
mu (Delta lx (Delta llx x _ _) ly (Delta _ _ lly y)) = Delta (lx ++ llx) x (ly ++ lly) y

instance Monad Delta where
    return x = Delta [] x [] x
    s >>= f  = mu $ fmap f s


returnS :: (Show s) => s -> Delta s
returnS x = Delta [(show x)] x [(show x)] x

returnSS :: (Show s) => s -> s -> Delta s
returnSS x y = Delta [(show x)] x [(show y)] y

-- samples

generator :: Int -> Delta [Int]
generator x = let intList = [1..x] in
                  returnS intList

primeFilter :: [Int] -> Delta [Int]
primeFilter xs = let primeList    = filter isPrime xs
                     refactorList = filter even xs    in
                 returnSS primeList refactorList

count :: [Int] -> Delta Int
count xs = let primeCount = length xs in
           returnS primeCount

primeCount :: Int -> Delta Int
primeCount x = generator x >>= primeFilter >>= count

bubbleSort :: [Int] -> Delta [Int]
bubbleSort = rightReverse . bubbleSortDelta . returnS

bubbleSortDelta :: Delta [Int] -> Delta [Int]
bubbleSortDelta (Delta lx [] ly []) = (Delta lx [] ly [])
bubbleSortDelta xs = fmapSS (\x -> (replicate maxNumCount maxNum) ++ x)
                            (\y -> (replicate minNumCount minNum) ++ y)
                            (bubbleSortDelta $ fmapSS remainListMax remainListMin xs)
    where
        leftValue      = deltaLeft xs
        rightValue     = deltaRight xs
        maxNum         = maximum leftValue
        minNum         = minimum rightValue
        remainListMax  = filter (/= maxNum)
        remainListMin  = filter (/= minNum)
        maxNumCount    = (length leftValue)  - (length $ remainListMax leftValue)
        minNumCount    = (length rightValue) - (length $ remainListMin rightValue)


rightReverse :: Delta [Int] -> Delta [Int]
rightReverse d = fmapSS id reverse d
