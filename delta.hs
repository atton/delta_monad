import Control.Applicative
import Data.Numbers.Primes -- $ cabal install primes

-- delta definition

data Delta a = Mono a | Delta a (Delta a) deriving Show

instance (Eq a) => Eq (Delta a) where
    (Mono x) == (Mono y)         = x == y
    (Mono _) == (Delta _ _)      = False
    (Delta x xs) == (Delta y ys) = (x == y) && (xs == ys)

-- basic functions

deltaAppend :: Delta a -> Delta a -> Delta a
deltaAppend (Mono x) d     = Delta x d
deltaAppend (Delta x d) ds = Delta x (deltaAppend d ds)

headDelta :: Delta a -> a
headDelta (Mono  x)   = x
headDelta (Delta x _) = x

tailDelta :: Delta a -> Delta a
tailDelta d@(Mono _)   = d
tailDelta (Delta _ ds) = ds

-- instance definitions

instance Functor Delta where
    fmap f (Mono x)    = Mono  (f x)
    fmap f (Delta x d) = Delta (f x) (fmap f d)

instance Applicative Delta where
    pure f                       = Mono  f
    (Mono f)     <*> (Mono x)    = Mono  (f x)
    df@(Mono f)  <*> (Delta x d) = Delta (f x) (df <*> d)
    (Delta f df) <*> d@(Mono x)  = Delta (f x) (df <*> d)
    (Delta f df) <*> (Delta x d) = Delta (f x) (df <*> d)

bind :: (Delta a) -> (a -> Delta b) -> (Delta b)
bind (Mono x)    f = f x
bind (Delta x d) f = Delta (headDelta (f x)) (bind d (tailDelta . f))

mu :: (Delta (Delta a)) -> (Delta a)
mu d = bind d id

instance Monad Delta where
    return x = Mono x
    d >>= f  = mu $ fmap f d



-- utils

returnS :: (Show s) => s -> Delta s
returnS x = Mono x

returnSS :: (Show s) => s -> s -> Delta s
returnSS x y = (returnS x) `deltaAppend` (returnS y)

deltaFromList :: [a] -> Delta a
deltaFromList = (foldl1 deltaAppend) . (fmap return)


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
bubbleSort [] = returnS []
bubbleSort xs = bubbleSort remainValue >>= (\xs -> returnSS (sortedValueL : xs)
                                                            (sortedValueR ++ xs))
    where
        maximumValue = maximum xs
        sortedValueL = maximumValue
        sortedValueR = replicate (length $ filter (== maximumValue) xs) maximumValue
        remainValue  = filter (/= maximumValue) xs
