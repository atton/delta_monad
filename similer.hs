data Similer a b = Similer a (a -> b) b

instance Functor (Similer a) where
  fmap g (Similer a f b) = Similer a (g . f) $ g b

eq :: (Eq a) => Similer a b -> Similer a b -> Bool
eq (Similer a _ _ ) (Similer b _ _) = a == b

eta :: a -> Similer a a
eta a = Similer a id a

mu :: (Eq b) => Similer a (Similer b c) -> Similer b c
mu (Similer a f b) = if (eq (f a) b) then b else undefined

double :: Int -> Int
double x = (2 * x)

twicePlus :: Int -> Int
twicePlus x = x + x

plusTwo :: Int -> Int
plusTwo x = x + 2

same :: (Show b, Eq b) => Similer a b -> b
same (Similer x f y) = if (f x) == y then y else (error ("not same :" ++ show y))

similer :: (Show b, Eq b) => (a -> b) -> (a -> b) -> a -> b
similer f g x = same $ Similer x g (f x)


-- samples
sameExample            = map (similer twicePlus double)  [1..10]
nonSameExample         = map (similer twicePlus plusTwo) [1..10]
nonSameExampleSpecific = map (similer twicePlus plusTwo) [2]
