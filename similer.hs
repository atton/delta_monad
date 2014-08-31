{-# LANGUAGE FlexibleContexts #-}
data Similer a f b = Similer a (a -> b) b

instance Functor (Similer a f) where
  fmap g (Similer a f b) = Similer a (g . f) $ g b

eta :: a -> Similer a (a -> a) a
eta a = Similer a id a

--mu :: (Eq (Similer b (b -> c) c)) => Similer a (a -> (Similer b (b -> c) c)) (Similer b (b -> c) c) -> Similer b (b -> c) c
mu :: (Eq (Similer b (b -> c) c)) => Similer a (a -> (Similer b (b -> c) c)) (Similer b (b -> c) c) -> Similer b (b -> c) c
mu (Similer a f b) = if ((f a) == b) then b else undefined
