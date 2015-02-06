module DeltaM (DeltaM(..), unDeltaM, appendDeltaM, tailDeltaM, headDeltaM, checkOut) where

import Control.Applicative
import Delta


-- DeltaM definition (Delta with Monad)

data DeltaM m a = DeltaM (Delta (m a)) deriving (Show)


-- DeltaM utils

unDeltaM :: DeltaM m a -> Delta (m a)
unDeltaM (DeltaM d) = d

headDeltaM :: DeltaM m a -> m a
headDeltaM (DeltaM d) = headDelta d

tailDeltaM :: DeltaM m a -> DeltaM m a
tailDeltaM (DeltaM d) = DeltaM $ tailDelta d

appendDeltaM :: DeltaM m a -> DeltaM m a -> DeltaM m a
appendDeltaM (DeltaM d) (DeltaM dd) = DeltaM (deltaAppend d dd)

checkOut :: Int -> DeltaM m a -> m a
checkOut 0 (DeltaM (Mono x))    = x
checkOut 0 (DeltaM (Delta x _)) = x
checkOut n (DeltaM (Mono x))    = x
checkOut n (DeltaM (Delta _ d)) = checkOut (n-1) (DeltaM d)


-- DeltaM instance definitions

instance (Functor m) => Functor (DeltaM m) where
    fmap f (DeltaM d) = DeltaM $ fmap (fmap f) d

instance (Applicative m) => Applicative (DeltaM m) where
    pure f                                          = DeltaM $ Mono $ pure f
    (DeltaM (Mono f))     <*> (DeltaM (Mono x))     = DeltaM $ Mono $ f <*> x
    df@(DeltaM (Mono f))  <*> (DeltaM (Delta x d))  = appendDeltaM (DeltaM $ Mono $ f <*> x) (df <*> (DeltaM d))
    (DeltaM (Delta f df)) <*> dx@(DeltaM (Mono x))  = appendDeltaM (DeltaM $ Mono $ f <*> x) ((DeltaM df) <*> dx)
    (DeltaM (Delta f df)) <*> (DeltaM (Delta x dx)) = appendDeltaM (DeltaM $ Mono $ f <*> x) ((DeltaM df) <*> (DeltaM dx))


mu' :: (Functor m, Monad m) => DeltaM m (DeltaM m a) -> DeltaM m a
mu' d@(DeltaM (Mono _))    = DeltaM $ Mono $ (>>= id) $ fmap headDeltaM $ headDeltaM d
mu' d@(DeltaM (Delta _ _)) = DeltaM $ Delta ((>>= id) $ fmap headDeltaM $ headDeltaM d)
                                            (unDeltaM (mu' (fmap tailDeltaM (tailDeltaM d))))

instance (Functor m, Monad m) => Monad (DeltaM m) where
    return x = DeltaM $ Mono $ return x
    d >>= f  = mu' $ fmap f d



