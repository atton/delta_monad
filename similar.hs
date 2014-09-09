import Control.Applicative

data Similar a = Single a | Similar a (Similar a) deriving (Show)

instance (Eq a) => Eq (Similar a) where
    s == ss = (same s) == (same ss)

same :: (Eq a) => Similar a -> a
same (Single x)    = x
same (Similar x s) = if x == (same s) then x else (error "same")

value :: Similar a -> a
value (Single x)    = x
value (Similar x s) = value s

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

instance Monad Similar where
    return              = Single
    (Single x)    >>= f = f x
    (Similar x s) >>= f = mu $ Similar (f x) (fmap f s)


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

