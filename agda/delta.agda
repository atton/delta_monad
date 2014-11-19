open import list
open import basic

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module delta where

DeltaLog : Set
DeltaLog = List String

data Delta {l : Level} (A : Set l) : (Set (suc l)) where
  mono    : DeltaLog -> A -> Delta A
  delta   : DeltaLog -> A -> Delta A -> Delta A

logAppend : {l : Level} {A : Set l} -> DeltaLog -> Delta A -> Delta A
logAppend l (mono lx x)    = mono  (l ++ lx) x
logAppend l (delta lx x d) = delta (l ++ lx) x (logAppend l d)

deltaAppend : {l : Level} {A : Set l} -> Delta A -> Delta A -> Delta A
deltaAppend (mono lx x) d     = delta lx x d
deltaAppend (delta lx x d) ds = delta lx x (deltaAppend d ds)

headDelta : {l : Level} {A : Set l} -> Delta A -> Delta A
headDelta (mono lx x)    = mono lx x
headDelta (delta lx x _) = mono lx x

tailDelta : {l : Level} {A : Set l} -> Delta A -> Delta A
tailDelta (mono lx x)   = mono lx x
tailDelta (delta _ _ d) = d


-- Functor
fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> (Delta A) -> (Delta B)
fmap f (mono lx x)    = mono lx (f x)
fmap f (delta lx x d) = delta lx (f x) (fmap f d)


{-# NO_TERMINATION_CHECK #-}
-- Monad (Category)
mu : {l : Level} {A : Set l} -> Delta (Delta A) -> Delta A
mu (mono ld d)     = logAppend ld d
mu (delta ld d ds) = deltaAppend (logAppend ld (headDelta d)) (mu (fmap tailDelta ds))

eta : {l : Level} {A : Set l} -> A -> Delta A
eta x = mono [] x

returnS : {l : Level} {A : Set l} -> A -> Delta A
returnS x = mono [[ (show x) ]] x

returnSS : {l : Level} {A : Set l} -> A -> A -> Delta A
returnSS x y = delta [[ (show x) ]] x (mono [[ (show y) ]] y)


-- Monad (Haskell)
return : {l : Level} {A : Set l} -> A -> Delta A
return = eta

_>>=_ : {l ll : Level} {A : Set l} {B : Set ll} ->
        (x : Delta A) -> (f : A -> (Delta B)) -> (Delta B)
x >>= f = mu (fmap f x)



-- proofs


-- Functor-laws

-- Functor-law-1 : T(id) = id'
functor-law-1 :  {l : Level} {A : Set l} ->  (d : Delta A) -> (fmap id) d ≡ id d
functor-law-1 (mono lx x)    = refl
functor-law-1 (delta lx x d) = cong (delta lx x) (functor-law-1 d)

-- Functor-law-2 : T(f . g) = T(f) . T(g)
functor-law-2 : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                (f : B -> C) -> (g : A -> B) -> (d : Delta A) ->
                (fmap (f ∙ g)) d ≡ ((fmap f) ∙ (fmap g)) d
functor-law-2 f g (mono lx x)    = refl
functor-law-2 f g (delta lx x d) = cong (delta lx (f (g x))) (functor-law-2 f g d)


{-
-- Monad-laws (Category)

-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (s : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) s) ≡ ((mu ∙ mu) s)
monad-law-1 (similar lx (similar llx (similar lllx x _ _) _ (similar _ _ _ _))
                     ly (similar   _ (similar _ _ _ _)  lly (similar _ _  llly y))) = begin
    similar (lx ++ (llx ++ lllx)) x (ly ++ (lly ++ llly)) y
  ≡⟨ cong (\left-list -> similar left-list x (ly ++ (lly ++ llly)) y) (list-associative lx llx lllx) ⟩
    similar (lx ++ llx ++ lllx) x (ly ++ (lly ++ llly)) y
  ≡⟨ cong (\right-list -> similar (lx ++ llx ++ lllx) x right-list y ) (list-associative ly lly llly) ⟩
    similar (lx ++ llx ++ lllx) x (ly ++ lly ++ llly) y
  ∎


-- monad-law-2 : join . fmap return = join . return = id
-- monad-law-2-1 join . fmap return = join . return
monad-law-2-1 : {l : Level} {A : Set l} -> (s : Delta  A) ->
  (mu ∙ fmap eta) s ≡ (mu ∙ eta) s
monad-law-2-1 (similar lx x ly y) = begin
    similar (lx ++ []) x (ly ++ []) y
  ≡⟨ cong (\left-list -> similar left-list x (ly ++ []) y) (empty-append lx)⟩
    similar lx x (ly ++ []) y
  ≡⟨ cong (\right-list -> similar lx x right-list y) (empty-append ly) ⟩
    similar lx x ly y
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
monad-law-h-1 a k = begin
    return a >>= k
  ≡⟨ refl ⟩
    mu (fmap k (return a))
  ≡⟨ refl ⟩
    mu (return (k a))
  ≡⟨ refl ⟩
    (mu ∙ return) (k a)
  ≡⟨ refl ⟩
    (mu ∙ eta) (k a)
  ≡⟨ (monad-law-2-2 (k a)) ⟩
    id (k a)
  ≡⟨ refl ⟩
    k a
  ∎

-- monad-law-h-2 : m >>= return  =  m
monad-law-h-2 : {l : Level}{A : Set l} -> (m : Delta A) -> (m >>= return)  ≡ m
monad-law-h-2 (similar lx x ly y) = monad-law-2-1 (similar lx x ly y)

-- monad-law-h-3 : m >>= (\x -> k x >>= h)  =  (m >>= k) >>= h
monad-law-h-3 : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                (m : Delta A)  -> (k : A -> (Delta B)) -> (h : B -> (Delta C)) ->
                (m >>= (\x -> k x >>= h)) ≡ ((m >>= k) >>= h)
monad-law-h-3 (similar lx x ly y) k h = begin
    ((similar lx x ly y) >>= (\x -> (k x) >>= h))
  ≡⟨ refl ⟩
    mu (fmap (\x -> k x >>= h) (similar lx x ly y))
  ≡⟨ refl ⟩
    (mu ∙ fmap (\x -> k x >>= h)) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ fmap (\x -> mu (fmap h (k x)))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ fmap (mu ∙ (\x -> fmap h (k x)))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (fmap mu ∙ (fmap (\x -> fmap h (k x))))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (fmap mu)) ((fmap (\x -> fmap h (k x))) (similar lx x ly y))
  ≡⟨ monad-law-1 (((fmap (\x -> fmap h (k x))) (similar lx x ly y))) ⟩
    (mu ∙ mu) ((fmap (\x -> fmap h (k x))) (similar lx x ly y))
  ≡⟨ refl ⟩
    (mu ∙ (mu ∙ (fmap (\x -> fmap h (k x))))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (mu ∙ (fmap ((fmap h) ∙ k)))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (mu ∙ ((fmap (fmap h)) ∙ (fmap k)))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (mu ∙ (fmap (fmap h)))) (fmap k (similar lx x ly y))
  ≡⟨ refl ⟩
    mu ((mu ∙ (fmap (fmap h))) (fmap k (similar lx x ly y)))
  ≡⟨ cong (\fx -> mu fx) (monad-law-4 h (fmap k (similar lx x ly y))) ⟩
    mu (fmap h (mu (similar lx (k x) ly (k y))))
  ≡⟨ refl ⟩
    (mu ∙ fmap h) (mu (fmap k (similar lx x ly y)))
  ≡⟨ refl ⟩
    mu (fmap h (mu (fmap k (similar lx x ly y))))
  ≡⟨ refl ⟩
    (mu (fmap k (similar lx x ly y))) >>= h
  ≡⟨ refl ⟩
    ((similar lx x ly y) >>= k) >>= h
  ∎
-}
