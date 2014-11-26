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

headDelta : {l : Level} {A : Set l} -> Delta A -> Delta A
headDelta (mono x)    = mono x
headDelta (delta x _) = mono x

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
bind (delta x d) f = deltaAppend (headDelta (f x)) (bind d (tailDelta ∙ f))

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
(delta x d) >>= f = deltaAppend (headDelta (f x)) (d >>= (tailDelta ∙ f))



-- proofs

-- sub proofs

head-delta-natural-transformation : {l ll : Level} {A : Set l} {B : Set ll} ->
                                  (f : A -> B) (d : Delta A) -> (headDelta (fmap f d)) ≡ fmap f (headDelta d)
head-delta-natural-transformation f (mono x)    = refl
head-delta-natural-transformation f (delta x d) = refl

tail-delta-natural-transfomation  : {l ll : Level} {A : Set l} {B : Set ll} ->
                                  (f : A -> B) (d : Delta A) -> (tailDelta (fmap f d)) ≡ fmap f (tailDelta d)
tail-delta-natural-transfomation f (mono x) = refl
tail-delta-natural-transfomation f (delta x d) = refl

delta-append-natural-transfomation : {l ll : Level} {A : Set l} {B : Set ll} ->
                                  (f : A -> B) (d : Delta A) (dd : Delta A) ->
                                  deltaAppend (fmap f d) (fmap f dd) ≡ fmap f (deltaAppend d dd)
delta-append-natural-transfomation f (mono x) dd    = refl
delta-append-natural-transfomation f (delta x d) dd = begin
  deltaAppend (fmap f (delta x d)) (fmap f dd)
  ≡⟨ refl ⟩
  deltaAppend (delta (f x) (fmap f d)) (fmap f dd)
  ≡⟨ refl ⟩
  delta (f x) (deltaAppend (fmap f d) (fmap f dd))
  ≡⟨ cong (\d -> delta (f x) d) (delta-append-natural-transfomation f d dd) ⟩
  delta (f x) (fmap f (deltaAppend d dd))
  ≡⟨ refl ⟩
  fmap f (deltaAppend (delta x d) dd)
  ∎
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

monad-law-1-1 : {l : Level} {A : Set l} -> (x : Delta A) -> (d : Delta (Delta (Delta A))) ->
  mu (delta x (fmap mu d)) ≡ mu (delta x (bind d tailDelta))
monad-law-1-1 (mono x) (mono (mono _)) = refl
monad-law-1-1 (mono x) (mono (delta (mono _) _)) = refl
monad-law-1-1 (mono x) (mono (delta (delta _ _) _)) = refl
monad-law-1-1 (mono x) (delta (mono (mono xx)) (mono d)) = begin
  mu (delta (mono x) (fmap mu (delta (mono (mono xx)) (mono d))))
  ≡⟨ refl ⟩
  mu (delta (mono x) (delta (mu (mono (mono xx))) (fmap mu (mono d))))
  ≡⟨ refl ⟩
  mu (delta (mono x) (delta (mono xx) (fmap mu (mono d))))
  ≡⟨ {!!} ⟩ -- ? 
  mu (delta (mono x) (delta (mono xx) ((tailDelta ∙ tailDelta)  d)))
  ≡⟨ refl ⟩
  mu (delta (mono x) (delta (mono xx) (bind (mono d) (tailDelta ∙ tailDelta))))
  ≡⟨ refl ⟩
  mu (delta (mono x) (deltaAppend (headDelta (tailDelta (mono (mono xx)))) (bind (mono d) (tailDelta ∙ tailDelta))))
  ≡⟨ refl ⟩
  mu (delta (mono x) (bind (delta (mono (mono xx)) (mono d)) tailDelta))
  ∎
monad-law-1-1 (mono x) (delta (mono (mono xx)) (delta d d₁)) = {!!}
monad-law-1-1 (mono x) (delta (mono (delta xx d)) ds) = {!!}
monad-law-1-1 (mono x) (delta (delta d d₁) d₂) = {!!}
monad-law-1-1 (delta x x₁) d = {!!}

-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) d) ≡ ((mu ∙ mu) d)
monad-law-1 (mono d)    = refl
monad-law-1 (delta (mono x) d)     = begin
  (mu ∙ fmap mu) (delta (mono x) d)
  ≡⟨ refl ⟩
  mu (fmap mu (delta (mono x) d))
  ≡⟨ refl ⟩
  mu (delta (mu (mono x)) (fmap mu d))
  ≡⟨ refl ⟩
  mu (delta x (fmap mu d))
  ≡⟨ monad-law-1-1 x d ⟩
  mu (delta x (bind d tailDelta))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta (mono x)) (bind d tailDelta))
  ≡⟨ refl ⟩
  mu (mu (delta (mono x) d))
  ≡⟨ refl ⟩
  (mu ∙ mu) (delta (mono x) d)
  ∎
monad-law-1 (delta (delta (mono x) xs) d) = begin
  (mu ∙ fmap mu) (delta (delta (mono x) xs) d)
  ≡⟨ refl ⟩
  mu (fmap mu (delta (delta (mono x) xs) d))
  ≡⟨ refl ⟩
  mu (delta (mu (delta (mono x) xs)) (fmap mu d))
  ≡⟨ refl ⟩
  mu (delta (deltaAppend (headDelta (mono x)) (bind xs tailDelta)) (fmap mu d))
  ≡⟨ refl ⟩
  mu (delta (delta x (bind xs tailDelta)) (fmap mu d))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (delta x (bind xs tailDelta))) (bind (fmap mu d) tailDelta)
  ≡⟨ refl ⟩
  delta x (bind (fmap mu d) tailDelta)
  ≡⟨ monad-law-1-1 (mono x) d ⟩
  mu (delta (mono x) (bind d tailDelta))
  ≡⟨ refl ⟩
  mu (deltaAppend (mono (mono x)) (bind d tailDelta))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta (delta (mono x) xs)) (bind d tailDelta))
  ≡⟨ refl ⟩
  mu (mu (delta (delta (mono x) xs) d))
  ≡⟨ refl ⟩
  (mu ∙ mu) (delta (delta (mono x) xs) d)
  ∎
monad-law-1 (delta (delta (delta x d) xs) ds) = begin
  (mu ∙ fmap mu) (delta (delta (delta x d) xs) ds)
  ≡⟨ refl ⟩
  mu (fmap mu (delta (delta (delta x d) xs) ds))
  ≡⟨ refl ⟩
  mu (delta (mu (delta (delta x d) xs)) (fmap mu ds))
  ≡⟨ refl ⟩
  mu (delta (deltaAppend (headDelta (delta x d)) (bind  xs tailDelta)) (fmap mu ds))
  ≡⟨ refl ⟩
  mu (delta (delta x (bind  xs tailDelta)) (fmap mu ds))
  ≡⟨ monad-law-1-1 (delta x d) ds ⟩
  mu (delta (delta x d) (bind ds tailDelta))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta (delta (delta x d) xs)) (bind ds tailDelta))
  ≡⟨ refl ⟩
  (mu ∙ mu) (delta (delta (delta x d) xs) ds)
  ∎

{-
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) d) ≡ ((mu ∙ mu) d)
monad-law-1 (mono d)    = refl
monad-law-1 (delta x (mono d))     = begin
  (mu ∙ fmap mu) (delta x (mono d))
  ≡⟨ refl ⟩
  mu ((fmap mu) (delta x (mono d)))
  ≡⟨ refl ⟩
  mu (delta (mu x) (fmap mu (mono d)))
  ≡⟨ refl ⟩
  mu (delta (mu x) (fmap mu (mono d)))
  ≡⟨ refl ⟩
  mu (delta (mu x) (mono (mu d)))
  ≡⟨ refl ⟩
  bind (delta (mu x) (mono (mu d))) id
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (bind (mono (mu d)) (tailDelta ∙ id))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (bind (mono (mu d)) (tailDelta))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (tailDelta (mu d))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) ((tailDelta ∙ mu) d)
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (bind (mono d) (tailDelta ∙ mu))
  ≡⟨ refl ⟩
  bind (delta x (mono d)) mu
  ≡⟨ {!!} ⟩
  mu (deltaAppend (headDelta x) (tailDelta d))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta x) (bind (mono d) tailDelta))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta (id x)) (bind (mono d) (tailDelta ∙ id)))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta x) (bind (mono d) (tailDelta ∙ id)))
  ≡⟨ refl ⟩
  mu (bind (delta x (mono d)) id)
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta (id x)) (bind  (mono d) (tailDelta ∙ id)))
  ≡⟨ refl ⟩
  mu (mu (delta x (mono d)))
  ≡⟨ refl ⟩
  (mu ∙ mu) (delta x (mono d))
  ∎
monad-law-1 (delta x (delta xx d)) = {!!}

monad-law-1 (delta x d) = begin
   (mu ∙ fmap mu) (delta x d)
   ≡⟨ refl ⟩
   mu ((fmap mu) (delta x d))
   ≡⟨ refl ⟩
   mu (delta (mu x) (fmap mu d))
   ≡⟨ refl ⟩
   bind (delta (mu x) (fmap mu d)) id
   ≡⟨ refl ⟩
   deltaAppend (headDelta (mu x)) (bind (fmap mu d) (tailDelta ∙ id))
   ≡⟨ refl ⟩
   deltaAppend (headDelta (mu x)) (bind (fmap mu d) (tailDelta ∙ id))
   ≡⟨ {!!} ⟩
   (mu ∙ mu) (delta x d)
   ∎




-- monad-law-2-2 :  join . return = id
monad-law-2-2 : {l : Level} {A : Set l } -> (s : Delta A) -> (mu ∙ eta) s ≡ id s
monad-law-2-2 (similar lx x ly y) = refl

-- monad-law-3 : return . f = fmap f . return
monad-law-3 : {l : Level} {A B : Set l} (f : A -> B) (x : A) -> (eta ∙ f) x ≡ (fmap f ∙ eta) x
monad-law-3 f x = refl

-- monad-law-4 : join . fmap (fmap f) = fmap f . join
monad-law-4 : {l ll : Level} {A : Set l} {B : Set ll} (f : A -> B) (s : Delta (Delta A)) ->
              (mu ∙ fmap (fmap f)) s ≡ (fmap f ∙ mu) s
monad-law-4 f (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = refl


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
monad-law-h-3 (delta x d) k h = begin
  (delta x d) >>= (\x -> k x >>= h)
  ≡⟨ refl ⟩
-- (delta x d) >>= f = deltaAppend (headDelta (f x)) (d >>= (tailDelta ∙ f))
  deltaAppend (headDelta ((\x -> k x >>= h) x)) (d >>= (tailDelta ∙ (\x -> k x >>= h)))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (k x >>= h)) (d >>= (tailDelta ∙ (\x -> k x >>= h)))
  ≡⟨ {!!} ⟩
  ((delta x d) >>= k) >>= h
  ∎
-}
