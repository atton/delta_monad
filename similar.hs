import Control.Applicative
import Data.Numbers.Primes -- $ cabal install primes

data Similar a = Similar [String] a [String] a deriving (Show)

value :: (Similar a) -> a
value (Similar _ x _ _) = x

similar :: (Similar a) -> a
similar (Similar _ _ _ y) = y

instance (Eq a) => Eq (Similar a) where
    s == ss = (value s) == (value ss)

instance Functor Similar where
    fmap f (Similar xs x ys y) = Similar xs (f x) ys (f y)

instance Applicative Similar where
    pure f                                      = Similar [] f [] f
    (Similar lf f lg g) <*> (Similar lx x ly y) = Similar (lf ++ lx) (f x) (lg ++ ly) (g y)

mu :: Similar (Similar a) -> Similar a
mu (Similar lx (Similar llx x _ _) ly (Similar _ _ lly y)) = Similar (lx ++ llx) x (ly ++ lly) y

instance Monad Similar where
    return x = Similar [] x [] x
    s >>= f  = mu $ fmap f s


returnS :: (Show s) => s -> Similar s
returnS x = Similar [(show x)] x [(show x)] x

-- samples

generator :: Int -> Similar [Int]
generator x = let intList = [1..x] in
                  returnS intList

primeFilter :: [Int] -> Similar [Int]
primeFilter xs = let primeList    = filter isPrime xs
                     refactorList = filter even xs     in
                 Similar [(show primeList)] primeList [(show refactorList)] refactorList

count :: [Int] -> Similar Int
count xs = let primeCount = length xs in
           returnS primeCount

primeCount :: Int -> Similar Int
primeCount x = generator x >>= primeFilter >>= count
