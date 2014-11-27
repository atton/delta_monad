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
  one : Int
  succ : Int -> Int

n-times-tail-delta : {l : Level} {A : Set l} -> Int -> ((Delta A) -> (Delta A))
n-times-tail-delta one = tailDelta
n-times-tail-delta (succ n) = (n-times-tail-delta n) ∙  tailDelta

tail-delta-to-mono : {l : Level} {A : Set l} -> (n : Int) -> (x : A) ->
  (n-times-tail-delta n) (mono x) ≡ (mono x)
tail-delta-to-mono one x = refl
tail-delta-to-mono (succ n) x = begin
  n-times-tail-delta (succ n) (mono x)
  ≡⟨ refl ⟩
  n-times-tail-delta n (mono x)
  ≡⟨ tail-delta-to-mono n x ⟩
  mono x
  ∎

monad-law-1-4 : {l : Level} {A : Set l} -> (n : Int) (d : Delta (Delta A)) -> 
  (headDelta ((n-times-tail-delta n) (headDelta ((n-times-tail-delta n) d)))) ≡ 
  (headDelta ((n-times-tail-delta n) (mu d)))
monad-law-1-4 one (mono d)     = refl
monad-law-1-4 one (delta d (mono ds)) = refl
monad-law-1-4 one (delta d (delta ds ds₁)) = refl
monad-law-1-4 (succ n) (mono d) = begin
  headDelta (n-times-tail-delta (succ n) (headDelta (n-times-tail-delta (succ n) (mono d))))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) (headDelta ((n-times-tail-delta n) (mono d))))
  ≡⟨ cong (\d -> headDelta (n-times-tail-delta (succ n) (headDelta d))) (tail-delta-to-mono n d) ⟩
  headDelta (n-times-tail-delta (succ n) (headDelta (mono d)))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) d)
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) (mu (mono d)))
  ∎
monad-law-1-4 (succ n) (delta d (mono ds)) = begin
  headDelta (n-times-tail-delta (succ n) (headDelta (n-times-tail-delta (succ n) (delta d (mono ds)))))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) (headDelta (n-times-tail-delta n (mono ds))))
  ≡⟨ cong (\d -> headDelta (n-times-tail-delta (succ n) (headDelta d))) (tail-delta-to-mono n ds) ⟩
  headDelta (n-times-tail-delta (succ n) (headDelta (mono ds)))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) ds)
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta n (tailDelta ds))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta n ((bind (mono ds) tailDelta)))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) (delta (headDelta d) (bind (mono ds) tailDelta)))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) (mu (delta d (mono ds))))
 ∎
monad-law-1-4 (succ n) (delta d (delta dd ds)) = begin
  headDelta (n-times-tail-delta (succ n) (headDelta (n-times-tail-delta (succ n) (delta d (delta dd ds)))))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) (headDelta (n-times-tail-delta n (delta dd ds))))
  ≡⟨ {!!} ⟩ -- ?  

  headDelta (n-times-tail-delta n (delta (headDelta (tailDelta dd)) (bind ds (tailDelta ∙ tailDelta))))
  ≡⟨ {!!} ⟩
  headDelta (n-times-tail-delta n (delta (headDelta (tailDelta dd)) (bind ds (tailDelta ∙ tailDelta ))))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta n (bind (delta dd ds) (tailDelta)))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) (delta (headDelta d) (bind (delta dd ds) (tailDelta))))
  ≡⟨ refl ⟩
  headDelta (n-times-tail-delta (succ n) (mu (delta d (delta dd ds))))
  ∎




monad-law-1-3 : {l : Level} {A : Set l} -> (i : Int) -> (d : Delta (Delta (Delta A))) -> 
  (bind (fmap mu d) (n-times-tail-delta i) ≡ (bind (bind d (n-times-tail-delta i)) (n-times-tail-delta i)))
monad-law-1-3 one (mono (mono d)) = refl
monad-law-1-3 one (mono (delta d d₁)) = refl
monad-law-1-3 one (delta d ds) = begin
  bind (fmap mu (delta d ds)) (n-times-tail-delta one) 
  ≡⟨ refl ⟩
  bind (delta (mu d) (fmap mu ds)) (n-times-tail-delta one) 
  ≡⟨ refl ⟩
  delta (headDelta ((n-times-tail-delta one) (mu d))) (bind (fmap mu ds) ((n-times-tail-delta one) ∙ tailDelta))
  ≡⟨ refl ⟩
  delta (headDelta ((n-times-tail-delta one) (mu d))) (bind (fmap mu ds) (n-times-tail-delta (succ one)))
  ≡⟨ cong (\dx -> delta (headDelta ((n-times-tail-delta one) (mu d))) dx) (monad-law-1-3 (succ one) ds) ⟩
  delta (headDelta ((n-times-tail-delta one) (mu d))) (bind (bind ds (n-times-tail-delta (succ one))) (n-times-tail-delta (succ one)))
  ≡⟨ cong (\dx -> delta dx (bind (bind ds (n-times-tail-delta (succ one))) (n-times-tail-delta (succ one )))) (sym (monad-law-1-4 one d)) ⟩
  delta (headDelta ((n-times-tail-delta one) (headDelta ((n-times-tail-delta one) d)))) (bind (bind ds (n-times-tail-delta (succ one))) (n-times-tail-delta (succ one)))
  ≡⟨ refl ⟩
  delta (headDelta ((n-times-tail-delta one) (headDelta ((n-times-tail-delta one) d)))) ((bind (bind ds (n-times-tail-delta (succ one)))) ((n-times-tail-delta one) ∙ tailDelta))
  ≡⟨ refl ⟩
  bind (delta (headDelta ((n-times-tail-delta one) d)) (bind ds (n-times-tail-delta (succ one)))) (n-times-tail-delta one)
  ≡⟨ refl ⟩
  bind (delta (headDelta ((n-times-tail-delta one) d)) (bind ds ((n-times-tail-delta one) ∙ tailDelta))) (n-times-tail-delta one)
  ≡⟨ refl ⟩
  bind (bind (delta d ds) (n-times-tail-delta one)) (n-times-tail-delta one)
  ∎
monad-law-1-3 (succ i) d = {!!}


monad-law-1-2 : {l : Level} {A : Set l} -> (d : Delta (Delta A)) -> headDelta (mu d) ≡ (headDelta (headDelta d))
monad-law-1-2 (mono _)    = refl
monad-law-1-2 (delta _ _) = refl

-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) d) ≡ ((mu ∙ mu) d)
monad-law-1 (mono d) = refl
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
  ≡⟨ cong (\d -> delta (headDelta (headDelta x)) d) (monad-law-1-3 one d) ⟩
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