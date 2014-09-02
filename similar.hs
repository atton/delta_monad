{-# LANGUAGE GADTs #-}

data Similar a = (Eq a) => Similar a (a -> a) a

instance (Eq a) => Eq (Similar a) where
  s == ss = same s == same ss

same :: (Eq a) => Similar a -> a
same (Similar x f y) = if (f x) == y then y else undefined

mu :: (Eq a) => Similar (Similar a) -> Similar a
mu (Similar a f b) = if ((f a) == b) then b else undefined

class EqFunctor f where
  eqmap :: (Eq a, Eq b) => (a -> b) -> f a -> f b

instance EqFunctor Similar where
  eqmap f s = Similar fs id fs
    where fs = f $ same s

class EqMonad m where
  (>>=) :: (Eq a, Eq b) => m a -> (a -> m b) -> m b
  return ::(Eq a) =>  a -> m a

instance EqMonad Similar where
  return x = Similar x id x
  s >>= f  = mu (eqmap f s)

similar :: (Eq a) => (a -> a) -> (a -> a) -> a -> a
similar f g x = same $ Similar x g (f x)



double :: Int -> Int
double x = (2 * x)

twicePlus :: Int -> Int
twicePlus x = x + x

plusTwo :: Int -> Int
plusTwo x = x + 2

-- samples

{-
*Main> same $ Main.return 100 Main.>>= (\x -> Similar x twicePlus  $ double x)
200

*Main> same $ Main.return 2 Main.>>= (\x -> Similar x plusTwo $ double x)
4

*Main> same $ Main.return 100 Main.>>= (\x -> Similar x plusTwo $ double x)
*** Exception: Prelude.undefined
-}

