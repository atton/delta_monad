import Control.Applicative
import Control.Monad.Writer
import Data.Numbers.Primes -- $ cabal install primes

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

returnDD :: (Show s) => s -> s -> Delta s
returnDD x y = (return x) `deltaAppend` (return y)

deltaFromList :: [a] -> Delta a
deltaFromList = (foldl1 deltaAppend) . (fmap return)


-- samples

generator :: Int -> Delta [Int]
generator x = let intList = [1..x] in
                  return intList

primeFilter :: [Int] -> Delta [Int]
primeFilter xs = let primeList    = filter isPrime xs
                     refactorList = filter even xs    in
                 returnDD primeList refactorList

count :: [Int] -> Delta Int
count xs = let primeCount = length xs in
           return primeCount

primeCount :: Int -> Delta Int
primeCount x = generator x >>= primeFilter >>= count

bubbleSort :: [Int] -> Delta [Int]
bubbleSort [] = return []
bubbleSort xs = bubbleSort remainValue >>= (\xs -> returnDD (sortedValueL : xs)
                                                            (sortedValueR ++ xs))
    where
        maximumValue = maximum xs
        sortedValueL = maximumValue
        sortedValueR = replicate (length $ filter (== maximumValue) xs) maximumValue
        remainValue  = filter (/= maximumValue) xs



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



-- DeltaM examples

-- DeltaM example utils
type DeltaLog     = Writer [String]
type DeltaWithLog = DeltaM DeltaLog

returnW :: (Show a) => a -> DeltaLog a
returnW x = do tell $ [show x]
               return x

dmap :: (m a -> b) -> DeltaM m a -> Delta b
dmap f (DeltaM d) = fmap f d

deltaWithLogFromList :: (Show a) => [a] -> DeltaWithLog a
deltaWithLogFromList xs = DeltaM $ deltaFromList $ fmap returnW xs


-- example : prime filter
-- usage   : runWriter $ checkOut 0 $ primeCountM 30  -- run specific version
--         : dmap runWriter $ primeCountM 30          -- run all version

generatorM :: Int -> DeltaWithLog [Int]
generatorM x = let intList = [1..x] in
                             DeltaM $ deltaFromList $ fmap returnW $ replicate 2 intList

primeFilterM :: [Int] -> DeltaWithLog [Int]
primeFilterM xs = let primeList    = filter isPrime xs
                      refactorList = filter even xs    in
                      DeltaM $ deltaFromList $ fmap returnW [primeList, refactorList]


countM :: [Int] -> DeltaWithLog Int
countM xs = let primeCount = length xs in
                DeltaM $ deltaFromList $ fmap returnW $ replicate 2 primeCount

primeCountM :: Int -> DeltaWithLog Int
primeCountM x = generatorM x >>= primeFilterM >>= countM