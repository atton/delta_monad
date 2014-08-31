data Similer a f b = Similer a (a -> b) b

instance Functor (Similer a f) where
  fmap g (Similer a f b) = Similer a (g . f) $ g b

eta :: a -> Similer a (a -> a) a
eta a = Similer a id a

--mu :: (Eq a, Eq b, Eq c) => Similer a (a -> b) (Similer b (b -> c) c) -> Similer b (b -> c) c
--mu (Similer a f (Similer b g c)) = if ((f a) == b) then Similer b g c else undefined
--mu (Similer a f (Similer b g c)) = if ((f a) == b) then Similer b g c else undefined
