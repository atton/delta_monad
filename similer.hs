{-# LANGUAGE GADTs, MultiParamTypeClasses #-}

data Similer a = (Eq a) => Similer a (a -> a) a

instance (Eq a) => Eq (Similer a) where
  s == ss = same s == same ss

same :: Similer a -> a
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

{-
eta :: a -> Similer a a
eta a = Similer a id a


double :: Int -> Int
double x = (2 * x)

twicePlus :: Int -> Int
twicePlus x = x + x

plusTwo :: Int -> Int
plusTwo x = x + 2


similer :: (Show b, Eq b) => (a -> b) -> (a -> b) -> a -> b
similer f g x = same $ Similer x g (f x)


-- samples
sameExample            = map (similer twicePlus double)  [1..10]
nonSameExample         = map (similer twicePlus plusTwo) [1..10]
nonSameExampleSpecific = map (similer twicePlus plusTwo) [2]
-}
