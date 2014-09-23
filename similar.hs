import Control.Applicative
import Data.Numbers.Primes -- $ cabal install primes

data Similar a = Single [String] a | Similar [String] a [String] a deriving (Show)

value :: (Similar a) -> Similar a
value (Similar xs x _ _) = Single xs x
value s                  = s

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


{-



-- samples
{-

generator :: Int -> Similar [Int]
generator x = return [1..x]

primeFilter :: [Int] -> Similar [Int]
primeFilter xs = return $ filter isPrime xs

count :: [Int] -> Similar Int
count xs = return $ length xs

primeCount :: Int -> Int
primeCount x = value $ generator x >>= primeFilter >>= count
-}


{-
same :: (Eq a) => Similar a -> a
same (Single x)    = x
same (Similar x s) = if x == (same s) then x else (error "same")


similar :: Similar a -> Similar a -> Similar a
similar (Single x) ss    = Similar x ss
similar (Similar x s) ss = Similar x (similar s ss)

instance Functor Similar where
   fmap f (Single a)    = Single (f a)
   fmap f (Similar a s) = Similar (f a) (fmap f s)

instance Applicative Similar where
    pure                 = Single
    (Single f)    <*> s  = fmap f s
    (Similar f s) <*> ss = similar (fmap f ss) (s <*> ss)

mu :: (Similar (Similar a)) -> Similar a
mu (Single s)     = s
mu (Similar s ss) = similar s (mu ss)



-- samples

double :: Int -> Similar Int
double x = Single (2 * x)

twicePlus :: Int -> Similar Int
twicePlus x = Similar (x + x) (double x)

plusTwo :: Int -> Similar Int
plusTwo x = Similar (x + 2) (double x)

-- samples

{-
- Similar as Functor
*Main> fmap (double ) (Single 1)
Single (Single 2)
*Main> fmap (twicePlus) (Single 1)
Single (Similar 2 (Single 2))
*Main> fmap (plusTwo) (Single 1)
Single (Similar 3 (Single 2))
*Main> fmap (fmap double)  (fmap (plusTwo   ) (Single 1))
Single (Similar (Single 6) (Single (Single 4)))
*Main> same $ fmap same $ fmap (fmap double)  (fmap (plusTwo   ) (Single 1))
*** Exception: same
*Main> same $ fmap same $ fmap (fmap double)  (fmap (plusTwo   ) (Single 2))
Single 8

- Similar as Applicative Functor
*Main> Single (\x -> x * x) <*> Single 100
Single 10000
*Main> Similar  (\x -> x * x) (Single (\x -> x * 3)) <*> Single 100
Similar 10000 (Single 300)
*Main> Similar  (\x -> x * x) (Single (\x -> x * 3)) <*> (Similar 100 (Single 200))
Similar 10000 (Similar 40000 (Similar 300 (Single 600)))

- Similar as Monad
*Main>  return 100 >>= double  >>= twicePlus
Similar 400 (Single 400)
*Main>  return 100 >>= double  >>= twicePlus >>= plusTwo
Similar 402 (Similar 800 (Similar 402 (Single 800)))

*Main> same $  return 100 >>= double  >>= twicePlus >>= plusTwo
*** Exception: same
*Main> same $  return 100 >>= double  >>= twicePlus
400

*Main> same $  return 100 >>= double  >>= twicePlus
400
*Main> same $  return 100 >>= double  >>= twicePlus >>= plusTwo
*** Exception: same
*Main> value  $  return 100 >>= double  >>= twicePlus >>= plusTwo
800

-}
-}
-}
