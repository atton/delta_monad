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
{-

mu-head-delta : {l : Level} {A : Set l} -> (d : Delta (Delta A)) -> mu (headDelta d) ≡ headDelta (mu d)
mu-head-delta (mono (mono x))    = refl
mu-head-delta (mono (delta x (mono xx))) = begin
 mu (headDelta (mono (delta x (mono xx))))
 ≡⟨ refl ⟩
 bind (headDelta (mono (delta x (mono xx)))) id
 ≡⟨ refl ⟩
 bind (delta x (mono xx)) return
 ≡⟨ refl ⟩
 deltaAppend (headDelta (return x)) (bind (mono xx) (tailDelta ∙ return))
 ≡⟨ refl ⟩
 deltaAppend (headDelta (return x)) ((tailDelta ∙ return) xx)
 ≡⟨ refl ⟩
 deltaAppend (headDelta (mono x)) (tailDelta (mono xx))
 ≡⟨ refl ⟩
 deltaAppend (mono x) (mono xx)
 ≡⟨ refl ⟩
 delta x (mono xx)
 ≡⟨ {!!} ⟩
 headDelta (delta x (mono xx))
 ≡⟨ refl ⟩
 headDelta (bind (mono (delta x (mono xx))) id)
 ≡⟨ refl ⟩
 headDelta (mu (mono (delta x (mono xx))))
  ∎
mu-head-delta (mono (delta x (delta x₁ d))) = {!!}
mu-head-delta (delta d dd) = {!!}
-}
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

monad-law-1-5 : {l : Level} {A : Set l} -> (ds : Delta (Delta A)) ->
  (tailDelta ∙ tailDelta) (bind ds tailDelta)
  ≡
  bind ((tailDelta ∙ tailDelta) ds) ((tailDelta ∙ tailDelta) ∙ tailDelta)
monad-law-1-5 (mono ds) = refl
monad-law-1-5 (delta (mono x) ds) = {!!}
monad-law-1-5 (delta (delta x d) ds) = {!!}

monad-law-1-4 : {l : Level} {A : Set l} -> (x : A) -> (ds : Delta (Delta (Delta A))) ->
  delta x (bind (fmap mu ds) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡
  bind (delta (mono x) (bind ds ((tailDelta ∙ tailDelta ) ∙ tailDelta))) (tailDelta ∙ tailDelta)
monad-law-1-4 x (mono (mono ds)) = refl
monad-law-1-4 x (mono (delta (mono xx) ds)) = begin
  delta x (bind (fmap mu (mono (delta (mono xx) ds))) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  delta x (bind (mono (mu (delta (mono xx) ds))) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  delta x (bind (mono (bind (delta (mono xx) ds) id)) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  delta x (bind (mono (deltaAppend (headDelta (mono xx)) (bind  ds tailDelta))) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  delta x (bind (mono (deltaAppend (mono xx) (bind  ds tailDelta))) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  delta x (bind (mono (delta xx (bind  ds tailDelta))) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  delta x ((tailDelta ∙ (tailDelta ∙ tailDelta)) (delta xx (bind  ds tailDelta)))
  ≡⟨ refl ⟩
  delta x ((tailDelta ∙ tailDelta) (bind ds tailDelta))
  ≡⟨ cong (\d -> delta x d) (monad-law-1-5 ds) ⟩
  delta x (bind ((tailDelta ∙ tailDelta) ds) ((tailDelta ∙ tailDelta) ∙ tailDelta))
  ≡⟨ refl ⟩
  deltaAppend (mono x) (bind ((tailDelta ∙ tailDelta) ds) ((tailDelta ∙ tailDelta) ∙ tailDelta))
  ≡⟨ refl ⟩
  deltaAppend (headDelta ((tailDelta ∙ tailDelta) (mono x))) (bind ((tailDelta ∙ tailDelta) ds) ((tailDelta ∙ tailDelta) ∙ tailDelta))
  ≡⟨ refl ⟩
  bind (delta (mono x) ((tailDelta ∙ tailDelta) ds)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩ 
  bind (delta (mono x) (bind (mono (delta (mono xx) ds)) ((tailDelta ∙ tailDelta) ∙ tailDelta))) (tailDelta ∙ tailDelta)
  ∎
monad-law-1-4 x (mono (delta (delta x₁ ds) ds₁)) = {!!}
monad-law-1-4 x (delta ds ds₁) = {!!}

monad-law-1-3 : {l : Level} {A : Set l} -> (ds : Delta (Delta A)) ->
  tailDelta (bind ds tailDelta) ≡ bind (tailDelta ds) (tailDelta ∙ tailDelta)
monad-law-1-3 (mono ds)              = refl
monad-law-1-3 (delta (mono x) ds)    = refl
monad-law-1-3 (delta (delta x (mono x₁)) ds) = refl
monad-law-1-3 (delta (delta x (delta x₁ d)) ds) = refl

monad-law-1-sub-sub : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) ->
  bind (fmap mu d) (tailDelta ∙ tailDelta) ≡ bind (bind d (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta)
monad-law-1-sub-sub (mono (mono d))            = refl
monad-law-1-sub-sub (mono (delta (mono x) ds)) = begin
  bind (fmap mu (mono (delta (mono x) ds))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (mono (mu (delta (mono x) ds))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (mono (bind (delta (mono x) ds) id)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (mono (deltaAppend (headDelta (mono x)) (bind ds tailDelta))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (mono (deltaAppend (mono x) (bind ds tailDelta))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (mono (delta x (bind ds tailDelta))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (delta x (bind ds tailDelta))
  ≡⟨ refl ⟩
  tailDelta (bind ds tailDelta)
  ≡⟨ monad-law-1-3 ds ⟩
  bind (tailDelta ds) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind ((tailDelta ∙ tailDelta) (delta (mono x) ds)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (bind (mono (delta (mono x) ds)) (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (bind (headDelta (tailDelta (mono (delta (mono x) ds)))) (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (bind (mono (delta (mono x) ds)) (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta)
  ∎
monad-law-1-sub-sub (mono (delta (delta x (mono x₁)) ds)) = begin
  bind (fmap mu (mono (delta (delta x (mono x₁)) ds))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (mono (mu (delta (delta x (mono x₁)) ds))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (mu (delta (delta x (mono x₁)) ds))
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (bind (delta (delta x (mono x₁)) ds) id)
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (deltaAppend (headDelta (delta x (mono x₁))) (bind ds (tailDelta ∙ id)))
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (deltaAppend (mono x) (bind ds (tailDelta ∙ id)))
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (delta x (bind ds (tailDelta ∙ id)))
  ≡⟨ refl ⟩
  tailDelta (bind ds (tailDelta ∙ id))
  ≡⟨ monad-law-1-3 ds ⟩
  bind (tailDelta ds) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind ((tailDelta ∙ tailDelta) (delta (delta x (mono x₁)) ds)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (bind (mono (delta (delta x (mono x₁)) ds))  (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta)
  ∎
monad-law-1-sub-sub (mono (delta (delta x (delta xx d)) ds)) = begin
  bind (fmap mu (mono (delta (delta x (delta xx d)) ds))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (mono (mu (delta (delta x (delta xx d)) ds))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (mu (delta (delta x (delta xx d)) ds))
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (bind (delta (delta x (delta xx d)) ds) id)
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (deltaAppend (headDelta (delta x (delta xx d))) (bind ds tailDelta))
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (deltaAppend (mono x) (bind ds tailDelta))
  ≡⟨ refl ⟩
  (tailDelta ∙ tailDelta) (delta x (bind ds tailDelta))
  ≡⟨ refl ⟩
  tailDelta (bind ds tailDelta)
  ≡⟨ monad-law-1-3 ds ⟩
  bind (tailDelta ds) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind ((tailDelta ∙ tailDelta) (delta (delta x (delta xx d)) ds)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (bind (mono (delta (delta x (delta xx d)) ds)) (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta)
  ∎
monad-law-1-sub-sub (delta (mono (mono x)) ds) = begin
  bind (fmap mu (delta (mono (mono x)) ds)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (delta (mu (mono (mono x))) (fmap mu ds)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (delta (mono x) (fmap mu ds)) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (headDelta ((tailDelta ∙ tailDelta) (mono x))) (bind (fmap mu ds) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  deltaAppend ((tailDelta ∙ tailDelta) (mono x)) (bind (fmap mu ds) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  deltaAppend (mono x) (bind (fmap mu ds) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  delta x (bind (fmap mu ds) (tailDelta ∙ (tailDelta ∙ tailDelta)))
  ≡⟨ monad-law-1-4 x ds ⟩ -- ?
  bind (delta (mono x) (bind ds ((tailDelta ∙ tailDelta ) ∙ tailDelta))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (delta (tailDelta (mono x)) (bind ds (tailDelta ∙ (tailDelta ∙ tailDelta)))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (deltaAppend (mono (mono x)) (bind ds (tailDelta ∙ (tailDelta ∙ tailDelta)))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (deltaAppend (headDelta ((tailDelta ∙ tailDelta) (mono (mono x)))) (bind ds (tailDelta ∙ (tailDelta ∙ tailDelta)))) (tailDelta ∙ tailDelta)
  ≡⟨ refl ⟩
  bind (bind (delta (mono (mono x)) ds) (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta)
  ∎
monad-law-1-sub-sub (delta (mono (delta x d)) ds) = {!!}
monad-law-1-sub-sub (delta (delta d d₁) ds) = {!!}


monad-law-1-sub : {l : Level} {A : Set l} -> (x : Delta (Delta A)) -> (d : Delta (Delta (Delta A))) ->
  deltaAppend (headDelta (mu x)) (bind (fmap mu d) tailDelta) ≡ mu (deltaAppend (headDelta x) (bind d tailDelta))
monad-law-1-sub (mono (mono _)) (mono (mono _)) = refl
monad-law-1-sub (mono (mono _)) (mono (delta (mono _) _)) = refl
monad-law-1-sub (mono (mono _)) (mono (delta (delta _ _) _)) = refl
monad-law-1-sub (mono (mono x)) (delta (mono (mono xx)) d) = begin
  deltaAppend (headDelta (mu (mono (mono x)))) (bind (fmap mu (delta (mono (mono xx)) d)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu (mono (mono x)))) (bind (delta (mu (mono (mono xx))) (fmap mu d)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (headDelta (bind (mono (mono x)) id)) (bind (delta (mu (mono (mono xx))) (fmap mu d)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mono x)) (bind (delta (mu (mono (mono xx))) (fmap mu d)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mono x)) (bind (delta (mono xx) (fmap mu d)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (mono x) (bind (delta (mono xx) (fmap mu d)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (mono x) (bind (delta (mono xx) (fmap mu d)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (mono x) (deltaAppend (tailDelta (mono xx)) (bind (fmap mu d) (tailDelta ∙  tailDelta)))
  ≡⟨ refl ⟩
  deltaAppend (mono x) (deltaAppend (mono xx) (bind (fmap mu d) (tailDelta ∙  tailDelta)))
  ≡⟨ refl ⟩
  deltaAppend (mono x) (deltaAppend (mu (mono (mono xx))) (bind (fmap mu d) (tailDelta ∙  tailDelta)))
  ≡⟨ refl ⟩
  deltaAppend (mono x) (deltaAppend (mono xx) (bind (fmap mu d) (tailDelta ∙  tailDelta)))
  ≡⟨ refl ⟩
  delta x (deltaAppend (mono xx) (bind (fmap mu d) (tailDelta ∙  tailDelta)))
  ≡⟨ refl ⟩
  delta x (delta xx (bind (fmap mu d) (tailDelta ∙  tailDelta)))
  ≡⟨ cong (\d -> (delta x (delta xx d))) (monad-law-1-sub-sub d) ⟩ -- ???
  delta x (delta xx (bind (bind d (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta)))
  ≡⟨ refl ⟩
  delta x ((deltaAppend (mono xx) (bind (bind d (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta))))
  ≡⟨ refl ⟩
  delta x ((deltaAppend (tailDelta (mono xx)) (bind (bind d (tailDelta ∙ tailDelta)) (tailDelta ∙ tailDelta))))
  ≡⟨ refl ⟩
  delta x (bind (delta (mono xx) (bind d (tailDelta ∙ tailDelta))) tailDelta)
  ≡⟨ refl ⟩
  delta x (bind (deltaAppend (mono (mono xx)) (bind d (tailDelta ∙ tailDelta))) tailDelta)
  ≡⟨ refl ⟩
  delta x (bind (deltaAppend (headDelta (tailDelta (mono (mono xx)))) (bind d (tailDelta ∙ tailDelta))) tailDelta)
  ≡⟨ refl ⟩
  delta x (bind (bind (delta (mono (mono xx)) d) tailDelta) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (mono x) (bind (bind (delta (mono (mono xx)) d) tailDelta) tailDelta)
  ≡⟨ refl ⟩
  bind (delta (mono x) (bind (delta (mono (mono xx)) d) tailDelta)) id
  ≡⟨ refl ⟩
  mu (delta (mono x) (bind (delta (mono (mono xx)) d) tailDelta))
  ≡⟨ refl ⟩
  mu (deltaAppend (mono (mono x)) (bind (delta (mono (mono xx)) d) tailDelta))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta (mono (mono x))) (bind (delta (mono (mono xx)) d) tailDelta))
 ∎
monad-law-1-sub (mono (mono x)) (delta (mono (delta x₁ d)) d₁) = {!!}
monad-law-1-sub (mono (mono x)) (delta (delta d d₁) d₂) = {!!}
monad-law-1-sub (mono (delta x x₁)) d = {!!}
monad-law-1-sub (delta x x₁) d = {!!}

-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) d) ≡ ((mu ∙ mu) d)
monad-law-1 (mono d)    = refl
monad-law-1 (delta x d) = begin
  (mu ∙ (fmap mu)) (delta x d)
  ≡⟨ refl ⟩
  mu (fmap mu (delta x d))
  ≡⟨ refl ⟩
  mu (delta (mu x) (fmap mu d))
  ≡⟨ refl ⟩
  bind (delta (mu x) (fmap mu d)) id
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (bind (fmap mu d) tailDelta)
  ≡⟨ monad-law-1-sub x d ⟩
  mu (deltaAppend (headDelta x) (bind d tailDelta))
  ≡⟨ refl ⟩
  mu (bind (delta x d) id)
  ≡⟨ refl ⟩
  mu (mu (delta x d))
  ≡⟨ refl ⟩
  (mu ∙ mu) (delta x d)
  ∎

-- split d
{-
monad-law-1 (delta x (mono d)) = begin

  (mu ∙ fmap mu) (delta x (mono d))
  ≡⟨ refl ⟩
  mu (fmap mu (delta x (mono d)))
  ≡⟨ refl ⟩
  mu (delta (mu x) (mono (mu d)))
  ≡⟨ refl ⟩
  bind (delta (mu x) (mono (mu d))) id
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (bind (mono (mu d)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (tailDelta (mu d))
  ≡⟨ {!!} ⟩
  mu (deltaAppend (headDelta x) (tailDelta d))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta x) (tailDelta (id d)))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta x) ((tailDelta ∙ id) d))
  ≡⟨ refl ⟩
  mu (deltaAppend (headDelta x) (bind  (mono d) (tailDelta ∙ id)))
  ≡⟨  refl ⟩
  mu (bind (delta x (mono d)) id)
  ≡⟨ refl ⟩
  mu (mu (delta x (mono d)))
  ≡⟨ refl ⟩
  (mu ∙ mu) (delta x (mono d))
  ∎
monad-law-1 (delta x (delta d ds)) = begin
  (mu ∙ fmap mu) (delta x (delta d ds))
  ≡⟨ refl ⟩
  mu (fmap mu (delta x (delta d ds)))
  ≡⟨ refl ⟩
  mu (delta (mu x) (delta (mu d) (fmap mu ds)))
  ≡⟨ refl ⟩
  bind (delta (mu x) (delta (mu d) (fmap mu ds))) id
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (bind (delta (mu d) (fmap mu ds)) tailDelta)
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu x)) (deltaAppend (headDelta (tailDelta (mu d))) (bind (fmap mu ds) (tailDelta ∙ tailDelta)))

  ≡⟨ {!!} ⟩
  (mu ∙ mu) (delta x (delta d ds))
  ∎
-}


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
