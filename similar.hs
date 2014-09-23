import Control.Applicative
import Data.Numbers.Primes -- $ cabal install primes

data Similar a = Single [String] a | Similar [String] a [String] a deriving (Show)

value :: (Similar a) -> a
value (Single  _ x)     = x
value (Similar _ x _ _) = x

similar :: (Similar a) -> a
similar (Single  _ x)     = x
similar (Similar _ _ _ y) = y

instance (Eq a) => Eq (Similar a) where
    s == ss = (value s) == (value ss)

instance Functor Similar where
    fmap f (Single xs x)       = Single  xs (f x)
    fmap f (Similar xs x ys y) = Similar xs (f x) ys (f y)

instance Applicative Similar where
    pure                                        = Single []
    (Single lf f)       <*> (Single lx x)       = Single  (lf ++ lx) (f x)
    (Single lf f)       <*> (Similar lx x ly y) = Similar (lf ++ lx) (f x) (lf ++ ly) (f y)
    (Similar lf f lg g) <*> (Single lx x)       = Similar (lf ++ lx) (f x) (lg ++ lx) (g x)
    (Similar lf f lg g) <*> (Similar lx x ly y) = Similar (lf ++ lx) (f x) (lg ++ ly) (g y)

mu :: Similar (Similar a) -> Similar a
mu (Single  ls (Single lx x))                              = Single  (ls ++ lx)  x
mu (Single  ls (Similar lx x ly y))                        = Similar (ls ++ lx)  x (ls ++ ly)  y
mu (Similar lx (Single llx x) ly (Single lly y))           = Similar (lx ++ llx) x (ly ++ lly) y
mu (Similar lx (Similar llx x _ _) ly (Similar _ _ lly y)) = Similar (lx ++ llx) x (lx ++ lly) y
mu _                                                       = error "Invalid Similar"

instance Monad Similar where
    return  = Single []
    s >>= f = mu $ fmap f s




-- samples

generator :: Int -> Similar [Int]
generator x = let intList = [1..x] in
                  Single [(show intList)] intList

primeFilter :: [Int] -> Similar [Int]
primeFilter xs = let primeList    = filter isPrime xs
                     refactorList = filter even xs     in
                 Similar [(show primeList)] primeList [(show refactorList)] refactorList

count :: [Int] -> Similar Int
count xs = let primeCount = length xs in
           Single [(show primeCount)] primeCount

primeCount :: Int -> Similar Int
primeCount x = generator x >>= primeFilter >>= count
