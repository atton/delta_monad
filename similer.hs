{-# LANGUAGE UndecidableInstances #-}
data Similer a b = Similer a (a -> b) b

instance Functor (Similer a) where
  fmap g (Similer a f b) = Similer a (g . f) $ g b

eq :: (Eq a) => Similer a b -> Similer a b -> Bool
eq (Similer a _ _ ) (Similer b _ _) = a == b

eta :: a -> Similer a a
eta a = Similer a id a

mu :: (Eq b) => Similer a (Similer b c) -> Similer b c
mu (Similer a f b) = if (eq (f a) b) then b else undefined

double :: Int -> Similer Int Int
double x = Similer (2 * x) id (2 * x)

twicePlus :: Int -> Similer Int (Similer Int Int)
twicePlus x = Similer x double (Similer (x + x) id $ x + x)

plusTwo :: Int -> Similer Int (Similer Int Int)
plusTwo x = Similer x double (Similer (x + 2) id (x + 2))

same :: Eq b => Similer a b -> b
same (Similer x f y) = if (f x) == y then y else undefined


-- samples

sameExample :: [Int]
sameExample = map same $ map (fmap same) $ fmap twicePlus [1..10]

nonSameExample :: [Int]
nonSameExample = map same $ map (fmap same) $ fmap plusTwo [1..10]

nonSameExampleSpecific :: [Int]
nonSameExampleSpecific = map same $ map (fmap same) $ fmap plusTwo [2]
