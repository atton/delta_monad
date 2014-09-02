{-# LANGUAGE UndecidableInstances #-}
data Similer a b = Similer a (a -> b) b

instance Functor (Similer a) where
  fmap g (Similer a f b) = Similer a (g . f) $ g b

same :: (Eq a) => Similer a b -> Similer a b -> Bool
same (Similer a _ _ ) (Similer b _ _) = a == b

eta :: a -> Similer a a
eta a = Similer a id a

mu :: (Eq b) => Similer a (Similer b c) -> Similer b c
mu (Similer a f b) = if (same (f a) b) then b else undefined

double :: Int -> Similer Int Int
double x = Similer (2 * x) id (2 * x)

twicePlus :: Int -> Similer Int (Similer Int Int)
twicePlus x = Similer x double (Similer (x + x) id $ x + x)

plusTwo :: Int -> Similer Int (Similer Int Int)
plusTwo x = Similer x double (Similer (x + 2) id (x + 2))

hoge :: Eq b => Similer a b -> b
hoge (Similer x f y) = if (f x) == y then y else undefined
