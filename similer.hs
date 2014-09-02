{-# LANGUAGE GADTs #-}

data Similer a = (Eq a) => Similer a (a -> a) a

instance (Eq a) => Eq (Similer a) where
  s == ss = same s == same ss

same :: (Eq a) => Similer a -> a
same (Similer x f y) = if (f x) == y then y else undefined

mu :: (Eq a) => Similer (Similer a) -> Similer a
mu (Similer a f b) = if ((f a) == b) then b else undefined

class EqFunctor f where
  eqmap :: (Eq a, Eq b) => (a -> b) -> f a -> f b

instance EqFunctor Similer where
  eqmap f s = Similer fs id fs
    where fs = f $ same s

class EqMonad m where
  (>>=) :: (Eq a, Eq b) => m a -> (a -> m b) -> m b
  return ::(Eq a) =>  a -> m a

instance EqMonad Similer where
  return x = Similer x id x
  s >>= f  = mu (eqmap f s)

similer :: (Eq a) => (a -> a) -> (a -> a) -> a -> a
similer f g x = same $ Similer x g (f x)



double :: Int -> Int
double x = (2 * x)

twicePlus :: Int -> Int
twicePlus x = x + x

plusTwo :: Int -> Int
plusTwo x = x + 2

-- samples

{-
*Main> same $ Main.return 100 Main.>>= (\x -> Similer x twicePlus  $ double x)
200

*Main> same $ Main.return 2 Main.>>= (\x -> Similer x plusTwo $ double x)
4

*Main> same $ Main.return 100 Main.>>= (\x -> Similer x plusTwo $ double x)
*** Exception: Prelude.undefined
-}
