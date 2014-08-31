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

instance (Eq a) => Monad (Similer a) where
        --return x = Similer x id x
        s >>= f  = mu (fmap f s)
