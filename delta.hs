import Control.Applicative
import Data.Numbers.Primes -- $ cabal install primes

type DeltaLog = [String]

data Delta a = Mono DeltaLog a | Delta DeltaLog a (Delta a) deriving Show

logAppend :: DeltaLog -> Delta a -> Delta a
logAppend l (Mono lx x)    = Mono (l ++ lx) x
logAppend l (Delta lx x d) = Delta (l ++ lx) x (logAppend l d)

deltaAppend :: Delta a -> Delta a -> Delta a
deltaAppend (Mono lx x) d = Delta lx x d
deltaAppend (Delta lx x d) ds = Delta lx x (deltaAppend d ds)

headDelta :: Delta a -> Delta a
headDelta d@(Mono _ _)   = d
headDelta (Delta lx x _) = Mono lx x

tailDelta :: Delta a -> Delta a
tailDelta d@(Mono _ _)   = d
tailDelta (Delta _ _ ds) = ds

instance Functor Delta where
    fmap f (Mono lx x)    = Mono  lx (f x)
    fmap f (Delta lx x d) = Delta lx (f x) (fmap f d)

instance Applicative Delta where
    pure f                             = Mono [] f
    (Mono lf f)     <*> (Mono lx x)    = Mono  (lf ++ lx) (f x)
    df@(Mono lf f)  <*> (Delta lx x d) = Delta (lf ++ lx) (f x) (df <*> d)
    (Delta lf f df) <*> d@(Mono lx x)  = Delta (lf ++ lx) (f x) (df <*> d)
    (Delta lf f df) <*> (Delta lx x d) = Delta (lf ++ lx) (f x) (df <*> d)


mu :: Delta (Delta a) -> Delta a
mu (Mono ld d)     = logAppend ld d
mu (Delta ld d ds) = (logAppend ld $ headDelta d) `deltaAppend` (mu $ fmap tailDelta ds)

instance Monad Delta where
    return x = Mono [] x
    d >>= f  = mu $ fmap f d

returnS :: (Show s) => s -> Delta s
returnS x = Mono [(show x)] x

returnSS :: (Show s) => s -> s -> Delta s
returnSS x y = (returnS x) `deltaAppend` (returnS y)


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
