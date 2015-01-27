open import list
open import basic
open import nat
open import laws

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module delta where

data Delta {l : Level} (A : Set l) : (Nat -> (Set l)) where
  mono    : A -> Delta A (S O)
  delta   : {n : Nat} -> A -> Delta A (S n) -> Delta A (S (S n))

deltaAppend : {l : Level} {A : Set l} {n m : Nat} -> Delta A (S n) -> Delta A (S m) -> Delta A ((S n) + (S m))
deltaAppend (mono x) d     = delta x d
deltaAppend (delta x d) ds = delta x (deltaAppend d ds)

headDelta : {l : Level} {A : Set l} {n : Nat} -> Delta A (S n) -> A
headDelta (mono x)    = x
headDelta (delta x _) = x

tailDelta : {l : Level} {A : Set l} {n : Nat} -> Delta A (S (S n)) -> Delta A (S n)
tailDelta (delta _ d) = d



-- Functor
delta-fmap : {l : Level} {A B : Set l} {n : Nat} -> (A -> B) -> (Delta A (S n)) -> (Delta B (S n))
delta-fmap f (mono x)    = mono  (f x)
delta-fmap f (delta x d) = delta (f x) (delta-fmap f d)



-- Monad (Category)
delta-eta : {l : Level} {A : Set l} {n : Nat} -> A -> Delta A (S n)
delta-eta {n = O}     x = mono x
delta-eta {n = (S n)} x = delta x (delta-eta {n = n} x)




delta-mu : {l : Level} {A : Set l} {n : Nat} -> (Delta (Delta A (S n)) (S n)) -> Delta A (S n)
delta-mu (mono x)    = x
delta-mu (delta x d) = delta (headDelta x) (delta-mu (delta-fmap tailDelta d))

delta-bind : {l : Level} {A B : Set l} {n : Nat} -> (Delta A (S n)) -> (A -> Delta B (S n)) -> Delta B (S n)
delta-bind d f = delta-mu (delta-fmap f d)

--delta-bind (mono x) f    = f x
--delta-bind (delta x d) f = delta (headDelta (f x)) (tailDelta (f x))


{-
-- Monad (Haskell)
delta-return : {l : Level} {A : Set l} -> A -> Delta A (S O)
delta-return = delta-eta

_>>=_ : {l : Level} {A B : Set l} {n : Nat} ->
        (x : Delta A n) -> (f : A -> (Delta B n)) -> (Delta B n)
d >>= f = delta-bind d f

-}

{-
-- proofs

-- sub-proofs

n-tail-plus : {l : Level} {A : Set l} -> (n : Nat) -> ((n-tail {l} {A} n) ∙ tailDelta) ≡ n-tail (S n)
n-tail-plus O     = refl
n-tail-plus (S n) = begin
  n-tail (S n) ∙ tailDelta             ≡⟨ refl ⟩
  (tailDelta ∙ (n-tail n)) ∙ tailDelta ≡⟨ refl ⟩
  tailDelta ∙ ((n-tail n) ∙ tailDelta) ≡⟨ cong (\t -> tailDelta ∙ t) (n-tail-plus n) ⟩
  n-tail (S (S n))
  ∎

n-tail-add : {l : Level} {A : Set l} {d : Delta A} -> (n m : Nat) -> (n-tail {l} {A} n) ∙ (n-tail m) ≡ n-tail (n + m)
n-tail-add O m = refl
n-tail-add (S n) O = begin
  n-tail (S n) ∙ n-tail O  ≡⟨ refl ⟩
  n-tail (S n)             ≡⟨ cong (\n -> n-tail n) (nat-add-right-zero (S n))⟩
  n-tail (S n + O)
  ∎
n-tail-add {l} {A} {d} (S n) (S m) =      begin
  n-tail (S n) ∙ n-tail (S m)             ≡⟨ refl ⟩
  (tailDelta ∙ (n-tail n)) ∙ n-tail (S m) ≡⟨ refl ⟩
  tailDelta ∙ ((n-tail n) ∙ n-tail (S m)) ≡⟨ cong (\t -> tailDelta ∙ t) (n-tail-add {l} {A} {d} n (S m)) ⟩
  tailDelta ∙ (n-tail (n + (S m)))        ≡⟨ refl ⟩
  n-tail (S (n + S m))                    ≡⟨ refl ⟩
  n-tail (S n + S m)                      ∎

tail-delta-to-mono : {l : Level} {A : Set l} -> (n : Nat) -> (x : A) ->
  (n-tail n) (mono x) ≡ (mono x)
tail-delta-to-mono O x     = refl
tail-delta-to-mono (S n) x =      begin
  n-tail (S n) (mono x)           ≡⟨ refl ⟩
  tailDelta (n-tail n (mono x))   ≡⟨ refl ⟩
  tailDelta (n-tail n (mono x))   ≡⟨ cong (\t -> tailDelta t) (tail-delta-to-mono n x) ⟩
  tailDelta (mono x)              ≡⟨ refl ⟩
  mono x                          ∎

head-delta-natural-transformation : {l : Level} {A B : Set l}
  -> (f : A -> B) -> (d : Delta A) -> headDelta (delta-fmap f d) ≡ f (headDelta d)
head-delta-natural-transformation f (mono x)    = refl
head-delta-natural-transformation f (delta x d) = refl

n-tail-natural-transformation  : {l  : Level} {A B : Set l} 
  -> (n : Nat) -> (f : A -> B) -> (d : Delta A) ->  n-tail n (delta-fmap f d) ≡ delta-fmap f (n-tail n d)
n-tail-natural-transformation O f d            = refl
n-tail-natural-transformation (S n) f (mono x) = begin
  n-tail (S n) (delta-fmap f (mono x))  ≡⟨ refl ⟩
  n-tail (S n) (mono (f x))       ≡⟨ tail-delta-to-mono (S n) (f x) ⟩
  (mono (f x))                    ≡⟨ refl ⟩
  delta-fmap f (mono x)                 ≡⟨ cong (\d -> delta-fmap f d) (sym (tail-delta-to-mono (S n) x)) ⟩
  delta-fmap f (n-tail (S n) (mono x))  ∎
n-tail-natural-transformation (S n) f (delta x d) = begin
  n-tail (S n) (delta-fmap f (delta x d))                 ≡⟨ refl ⟩
  n-tail (S n) (delta (f x) (delta-fmap f d))             ≡⟨ cong (\t -> t (delta (f x) (delta-fmap f d))) (sym (n-tail-plus n)) ⟩
  ((n-tail n) ∙ tailDelta) (delta (f x) (delta-fmap f d)) ≡⟨ refl ⟩
  n-tail n (delta-fmap f d)                               ≡⟨ n-tail-natural-transformation n f d ⟩
  delta-fmap f (n-tail n d)                               ≡⟨ refl ⟩
  delta-fmap f (((n-tail n) ∙ tailDelta) (delta x d))     ≡⟨ cong (\t -> delta-fmap f (t (delta x d))) (n-tail-plus n) ⟩
  delta-fmap f (n-tail (S n) (delta x d))                 ∎
-}
