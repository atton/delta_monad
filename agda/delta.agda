open import list
open import basic

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module delta where


data Delta {l : Level} (A : Set l) : (Set (suc l)) where
  mono    : A -> Delta A
  delta   : A -> Delta A -> Delta A

deltaAppend : {l : Level} {A : Set l} -> Delta A -> Delta A -> Delta A
deltaAppend (mono x) d     = delta x d
deltaAppend (delta x d) ds = delta x (deltaAppend d ds)

headDelta : {l : Level} {A : Set l} -> Delta A -> A
headDelta (mono x)    = x
headDelta (delta x _) = x

tailDelta : {l : Level} {A : Set l} -> Delta A -> Delta A
tailDelta (mono x)     = mono x
tailDelta (delta  _ d) = d


-- Functor
fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> (Delta A) -> (Delta B)
fmap f (mono x)    = mono (f x)
fmap f (delta x d) = delta (f x) (fmap f d)



-- Monad (Category)
eta : {l : Level} {A : Set l} -> A -> Delta A
eta x = mono x

bind : {l ll : Level} {A : Set l} {B : Set ll} -> (Delta A) -> (A -> Delta B) -> Delta B
bind (mono x)    f = f x
bind (delta x d) f = delta (headDelta (f x)) (bind d (tailDelta ∙ f))

mu : {l : Level} {A : Set l} -> Delta (Delta A) -> Delta A
mu d = bind d id

returnS : {l : Level} {A : Set l} -> A -> Delta A
returnS x = mono x

returnSS : {l : Level} {A : Set l} -> A -> A -> Delta A
returnSS x y = deltaAppend (returnS x) (returnS y)


-- Monad (Haskell)
return : {l : Level} {A : Set l} -> A -> Delta A
return = eta

_>>=_ : {l ll : Level} {A : Set l} {B : Set ll} ->
        (x : Delta A) -> (f : A -> (Delta B)) -> (Delta B)
(mono x) >>= f    = f x
(delta x d) >>= f = delta (headDelta (f x)) (d >>= (tailDelta ∙ f))



-- proofs

-- Functor-laws

-- Functor-law-1 : T(id) = id'
functor-law-1 :  {l : Level} {A : Set l} ->  (d : Delta A) -> (fmap id) d ≡ id d
functor-law-1 (mono x)    = refl
functor-law-1 (delta x d) = cong (delta x) (functor-law-1 d)

-- Functor-law-2 : T(f . g) = T(f) . T(g)
functor-law-2 : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                (f : B -> C) -> (g : A -> B) -> (d : Delta A) ->
                (fmap (f ∙ g)) d ≡ ((fmap f) ∙ (fmap g)) d
functor-law-2 f g (mono x)    = refl
functor-law-2 f g (delta x d) = cong (delta (f (g x))) (functor-law-2 f g d)


-- Monad-laws (Category)


data Int : Set where
  O  : Int
  S : Int -> Int

_+_ : Int -> Int -> Int
O + n = n
(S m) + n = S (m + n)

n-tail : {l : Level} {A : Set l} -> Int -> ((Delta A) -> (Delta A))
n-tail O = id
n-tail (S n) =  (n-tail n) ∙ tailDelta

postulate n-tail-plus : (n : Int) -> (tailDelta ∙ (n-tail n)) ≡ n-tail (S n)





tail-delta-to-mono : {l : Level} {A : Set l} -> (n : Int) -> (x : A) ->
  (n-tail n) (mono x) ≡ (mono x)
tail-delta-to-mono O x = refl
tail-delta-to-mono (S n) x = begin 
  n-tail (S n) (mono x)  ≡⟨ refl ⟩
  ((n-tail n) ∙ tailDelta) (mono x) ≡⟨ refl ⟩
  (n-tail n) (tailDelta (mono x))  ≡⟨ refl ⟩
  (n-tail n) (mono x)  ≡⟨ tail-delta-to-mono n x ⟩
  mono x
  ∎
{- begin
  n-tail (S n) (mono x)           ≡⟨ refl ⟩
  tailDelta (n-tail n (mono x))   ≡⟨ refl ⟩
  tailDelta (n-tail n (mono x))   ≡⟨ cong (\t -> tailDelta t) (tail-delta-to-mono n x) ⟩
  tailDelta (mono x)              ≡⟨ refl ⟩
  mono x
  ∎
-}
monad-law-1-2 : {l : Level} {A : Set l} -> (d : Delta (Delta A)) -> headDelta (mu d) ≡ (headDelta (headDelta d))
monad-law-1-2 (mono _) = refl
monad-law-1-2 (delta _ _) = refl

monad-law-1-3 : {l : Level} {A : Set l} -> (n : Int) -> (d : Delta (Delta (Delta A))) ->
  bind (fmap mu d) (n-tail n) ≡ bind (bind d (n-tail n)) (n-tail n)
monad-law-1-3 O (mono d)     = refl
monad-law-1-3 O (delta d ds) = begin
  bind (fmap mu (delta d ds)) (n-tail O) ≡⟨ refl ⟩ 
  bind (delta (mu d) (fmap mu ds)) (n-tail O) ≡⟨ refl ⟩ 
  delta (headDelta (mu d)) (bind (fmap mu ds) tailDelta) ≡⟨ cong (\dx -> delta dx (bind (fmap mu ds) tailDelta)) (monad-law-1-2 d) ⟩ 
  delta (headDelta (headDelta d)) (bind (fmap mu ds) tailDelta) ≡⟨ cong (\dx -> delta (headDelta (headDelta d)) dx) (monad-law-1-3 (S O) ds) ⟩ 
  delta (headDelta (headDelta d)) (bind (bind ds tailDelta) tailDelta) ≡⟨ refl ⟩
  bind (delta (headDelta d) (bind ds tailDelta)) (n-tail O) ≡⟨ refl ⟩
  bind (bind (delta d ds) (n-tail O)) (n-tail O)
  ∎
monad-law-1-3 (S n) (mono (mono d)) = begin
  bind (fmap mu (mono (mono d))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (mono d) (n-tail (S n)) ≡⟨ refl ⟩
  (n-tail (S n)) d ≡⟨ refl ⟩
  bind (mono d) (n-tail (S n)) ≡⟨ cong (\t -> bind t (n-tail (S n))) (sym (tail-delta-to-mono (S n) d))⟩
  bind (n-tail (S n) (mono d)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (n-tail (S n) (mono d)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (mono (mono d)) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (mono (delta d ds)) = begin
  bind (fmap mu (mono (delta d ds))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (mono (mu (delta d ds))) (n-tail (S n)) ≡⟨ refl ⟩
  n-tail (S n) (mu (delta d ds))  ≡⟨ refl ⟩
  n-tail (S n) (delta (headDelta d) (bind ds tailDelta))  ≡⟨ refl ⟩
  n-tail n (bind ds tailDelta)  ≡⟨ {!!} ⟩
  bind (n-tail n ds) (n-tail (S n)) ≡⟨ refl ⟩
  bind (n-tail (S n) (delta d ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (mono (delta d ds)) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (delta (mono d) ds) = begin
  bind (fmap mu (delta (mono d) ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (delta (mu (mono d)) (fmap mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (delta d (fmap mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ {!!} ⟩
  delta (headDelta ((n-tail (S n)) d)) (bind (fmap mu ds) (n-tail (S (S n)))) ≡⟨ {!!} ⟩
  delta (headDelta ((n-tail (S n)) d)) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (mono d)))) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ cong (\de -> delta (headDelta ((n-tail (S n)) (headDelta de))) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n))))) (sym (tail-delta-to-mono (S n) d)) ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) (mono d))))) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ refl ⟩
  bind (delta (headDelta ((n-tail (S n)) (mono d))) (bind ds (tailDelta ∙ (n-tail (S n))))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (delta (mono d) ds) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (delta (delta d dd) ds) = begin
  bind (fmap mu (delta (delta d dd) ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (delta (mu (delta d dd)) (fmap mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (mu (delta d dd)))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (delta (headDelta d) (bind dd tailDelta)))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail n) (bind dd tailDelta))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ {!!} ⟩

  delta (headDelta ((n-tail (S n)) (headDelta (n-tail n dd)))) (bind (bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) (delta d dd))))) (bind (bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  bind (delta (headDelta ((n-tail (S n)) (delta d dd))) (bind  ds (tailDelta ∙ (n-tail (S n))))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (delta (delta d dd) ds) (n-tail (S n))) (n-tail (S n))
  ∎

{-
monad-law-1-3 (S n) (mono d) = begin
 bind (fmap mu (mono d)) (n-tail (S n)) ≡⟨ refl ⟩
 bind (mono (mu d)) (n-tail (S n)) ≡⟨ refl ⟩
 n-tail (S n) (mu d) ≡⟨ {!!} ⟩
 bind (n-tail (S n) d) (n-tail (S n)) ≡⟨ refl ⟩
 bind (bind (mono d) (n-tail (S n))) (n-tail (S n))
 ∎
monad-law-1-3 (S n) (delta d ds) = begin
  bind (fmap mu (delta d ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (delta (mu d) (fmap mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (mu d))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (mu d))) (bind (fmap mu ds) (n-tail (S (S n)))) ≡⟨ {!!} ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) d)))) (bind (bind ds (n-tail (S (S n)))) (n-tail (S (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) d)))) (bind (bind ds (n-tail (S (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) d)))) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  bind (delta (headDelta ((n-tail (S n)) d)) (bind ds (tailDelta ∙ (n-tail (S n))))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (delta d ds) (n-tail (S n))) (n-tail (S n))
  ∎
-}

-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) d) ≡ ((mu ∙ mu) d)
monad-law-1 (mono d)    = refl
{-
monad-law-1 (delta x (mono d)) = begin
  (mu ∙ fmap mu) (delta x (mono d)) ≡⟨ refl ⟩
  mu (fmap mu (delta x (mono d))) ≡⟨ refl ⟩
  mu (delta (mu x) (mono (mu d))) ≡⟨ refl ⟩
  delta (headDelta (mu x)) (bind (mono (mu d)) tailDelta) ≡⟨ refl ⟩
  delta (headDelta (mu x)) (tailDelta (mu d)) ≡⟨ cong (\dx -> delta dx (tailDelta (mu d))) (monad-law-1-2 x) ⟩
  delta (headDelta (headDelta x)) (tailDelta (mu d)) ≡⟨ {!!} ⟩
  delta (headDelta (headDelta x)) (bind (tailDelta d) tailDelta)  ≡⟨ refl ⟩
  mu (delta (headDelta x) (tailDelta d))  ≡⟨ refl ⟩
  mu (delta (headDelta x) (bind (mono d) tailDelta))  ≡⟨ refl ⟩
  mu (mu (delta x (mono d)))  ≡⟨ refl ⟩
  (mu ∙ mu) (delta x (mono d))
  ∎
monad-law-1 (delta x (delta d ds)) = begin
  (mu ∙ fmap mu) (delta x (delta d ds)) ≡⟨ refl ⟩
  mu (fmap mu (delta x (delta d ds))) ≡⟨ refl ⟩
  mu (delta (mu x) (delta (mu d) (fmap mu ds))) ≡⟨ refl ⟩
  delta (headDelta (mu x)) (bind (delta (mu d) (fmap mu ds)) tailDelta) ≡⟨ refl ⟩
  delta (headDelta (mu x)) (delta (headDelta (tailDelta (mu d))) (bind (fmap mu ds) (tailDelta ∙ tailDelta))) ≡⟨ {!!} ⟩
  delta (headDelta (headDelta x)) (delta (headDelta (tailDelta (headDelta (tailDelta d)))) (bind (bind ds (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta))) ≡⟨ refl ⟩
  delta (headDelta (headDelta x)) (bind (delta (headDelta (tailDelta d)) (bind ds (tailDelta ∙ tailDelta))) tailDelta) ≡⟨ refl ⟩
  delta (headDelta (headDelta x)) (bind (bind (delta d ds) tailDelta) tailDelta) ≡⟨ refl ⟩
  mu (delta (headDelta x) (bind (delta d ds) tailDelta)) ≡⟨ refl ⟩
  mu (mu (delta x (delta d ds))) ≡⟨ refl ⟩
  (mu ∙ mu) (delta x (delta d ds))
  ∎
-}

monad-law-1 (delta x d) = begin
  (mu ∙ fmap mu) (delta x d)
  ≡⟨ refl ⟩
  mu (fmap mu (delta x d))
  ≡⟨ refl ⟩
  mu (delta (mu x) (fmap mu d))
  ≡⟨ refl ⟩
  delta (headDelta (mu x)) (bind (fmap mu d) tailDelta)
  ≡⟨ cong (\x -> delta x (bind (fmap mu d) tailDelta)) (monad-law-1-2 x) ⟩
  delta (headDelta (headDelta x)) (bind (fmap mu d) tailDelta)
  ≡⟨ cong (\d -> delta (headDelta (headDelta x)) d) (monad-law-1-3 (S O) d) ⟩
  delta (headDelta (headDelta x)) (bind (bind d tailDelta) tailDelta)
  ≡⟨ refl ⟩
  mu (delta (headDelta x) (bind d tailDelta))
  ≡⟨ refl ⟩
  mu (mu (delta x d))
  ≡⟨ refl ⟩
  (mu ∙ mu) (delta x d)
  ∎



{-
-- monad-law-2 : join . fmap return = join . return = id
-- monad-law-2-1 join . fmap return = join . return
monad-law-2-1 : {l : Level} {A : Set l} -> (d : Delta A) ->
  (mu ∙ fmap eta) d ≡ (mu ∙ eta) d
monad-law-2-1 (mono x) = refl
monad-law-2-1 (delta x d) = {!!}


-- monad-law-2-2 :  join . return = id
monad-law-2-2 : {l : Level} {A : Set l } -> (d : Delta A) -> (mu ∙ eta) d ≡ id d
monad-law-2-2 d = refl


-- monad-law-3 : return . f = fmap f . return
monad-law-3 : {l : Level} {A B : Set l} (f : A -> B) (x : A) -> (eta ∙ f) x ≡ (fmap f ∙ eta) x
monad-law-3 f x = refl


-- monad-law-4 : join . fmap (fmap f) = fmap f . join
monad-law-4 : {l ll : Level} {A : Set l} {B : Set ll} (f : A -> B) (d : Delta (Delta A)) ->
              (mu ∙ fmap (fmap f)) d ≡ (fmap f ∙ mu) d
monad-law-4 f d = {!!}




-- Monad-laws (Haskell)
-- monad-law-h-1 : return a >>= k  =  k a
monad-law-h-1 : {l ll : Level} {A : Set l} {B : Set ll} ->
                (a : A) -> (k : A -> (Delta B)) ->
                (return a >>= k)  ≡ (k a)
monad-law-h-1 a k = refl



-- monad-law-h-2 : m >>= return  =  m
monad-law-h-2 : {l : Level}{A : Set l} -> (m : Delta A) -> (m >>= return)  ≡ m
monad-law-h-2 (mono x)    = refl
monad-law-h-2 (delta x d) = cong (delta x) (monad-law-h-2 d)


-- monad-law-h-3 : m >>= (\x -> k x >>= h)  =  (m >>= k) >>= h
monad-law-h-3 : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                (m : Delta A)  -> (k : A -> (Delta B)) -> (h : B -> (Delta C)) ->
                (m >>= (\x -> k x >>= h)) ≡ ((m >>= k) >>= h)
monad-law-h-3 (mono x) k h    = refl
monad-law-h-3 (delta x d) k h = {!!}

-}
