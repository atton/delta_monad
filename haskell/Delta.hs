module Delta ( Delta(..) , deltaAppend , headDelta , tailDelta , deltaFromList) where

import Control.Applicative


-- Delta definition

data Delta a = Mono a | Delta a (Delta a) deriving Show

instance (Eq a) => Eq (Delta a) where
    (Mono x) == (Mono y)         = x == y
    (Mono _) == (Delta _ _)      = False
    (Delta x xs) == (Delta y ys) = (x == y) && (xs == ys)

-- basic functions

deltaAppend :: Delta a -> Delta a -> Delta a
deltaAppend (Mono x) d     = Delta x d
deltaAppend (Delta x d) ds = Delta x (deltaAppend d ds)

headDelta :: Delta a -> a
headDelta (Mono  x)   = x
headDelta (Delta x _) = x

tailDelta :: Delta a -> Delta a
tailDelta d@(Mono _)   = d
tailDelta (Delta _ ds) = ds

-- instance definitions

instance Functor Delta where
    fmap f (Mono x)    = Mono  (f x)
    fmap f (Delta x d) = Delta (f x) (fmap f d)

instance Applicative Delta where
    pure f                       = Mono  f
    (Mono f)     <*> (Mono x)    = Mono  (f x)
    df@(Mono f)  <*> (Delta x d) = Delta (f x) (df <*> d)
    (Delta f df) <*> d@(Mono x)  = Delta (f x) (df <*> d)
    (Delta f df) <*> (Delta x d) = Delta (f x) (df <*> d)

bind :: (Delta a) -> (a -> Delta b) -> (Delta b)
bind (Mono x)    f = f x
bind (Delta x d) f = Delta (headDelta (f x)) (bind d (tailDelta . f))

mu :: (Delta (Delta a)) -> (Delta a)
mu d = bind d id

instance Monad Delta where
    return x = Mono x
    d >>= f  = mu $ fmap f d

-- utils

deltaFromList :: [a] -> Delta a
deltaFromList = (foldl1 deltaAppend) . (fmap return)
