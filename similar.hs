data Similar a = Single a | Similar a (Similar a) deriving (Show)

instance (Eq a) => Eq (Similar a) where
    s == ss = (same s) == (same ss)

same :: (Eq a) => Similar a -> a
same (Single x)    = x
same (Similar x s) = if x == (same s) then x else (error "same")


instance Functor Similar where
   fmap f (Single a)    = Single (f a)
   fmap f (Similar a s) = Similar (f a) (fmap f s)

mu :: (Eq a) => (Similar (Similar a)) -> Similar a
mu (Single x)                 = x
mu (Similar (Single x) s)     = Similar x (mu s)
mu (Similar s ss) = Similar (same s) (mu ss)

{-
instance Monad Similar where
    return              = Single
    (Single x)    >>= f = f x
    (Similar x s) >>= f = mu $ Similar (f x) (fmap f s)
-}



double :: Int -> Similar Int
double x = Single (2 * x)

twicePlus :: Int -> Similar Int
twicePlus x = Similar (x + x) (double x)

plusTwo :: Int -> Similar Int
plusTwo x = Similar (x + 2) (double x)

-- samples

{-
*Main> same $ Main.return 100 Main.>>= (\x -> Similar x twicePlus  $ double x)
200

*Main> same $ Main.return 2 Main.>>= (\x -> Similar x plusTwo $ double x)
4

*Main> same $ Main.return 100 Main.>>= (\x -> Similar x plusTwo $ double x)
*** Exception: Prelude.undefined
-}

