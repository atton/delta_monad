data Similar a = Single a | Similar a (Similar a)

same :: (Eq a) => Similar a -> a
same (Single x)    = x
same (Similar x s) = if x == (same s) then x else undefined

instance (Eq a) => Eq (Similar a) where
    s == ss = (same s) == (same ss)

instance Functor Similar where
   fmap f (Single a)    = Single (f a)
   fmap f (Similar a s) = Similar (f a) (fmap f s)

{-

mu :: (Eq a) => Similar (Similar a) -> Similar a
mu (Similar a f b) = if ((f a) == b) then b else undefined

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

-}
