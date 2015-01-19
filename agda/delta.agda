open import list
open import basic
open import nat
open import laws

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module delta where


data Delta {l : Level} (A : Set l) : (Set l) where
  mono    : A -> Delta A
  delta   : A -> Delta A -> Delta A

deltaAppend : {l : Level} {A : Set l} -> Delta A -> Delta A -> Delta A
deltaAppend (mono x) d     = delta x d
deltaAppend (delta x d) ds = delta x (deltaAppend d ds)

headDelta : {l : Level} {A : Set l} -> Delta A -> A
headDelta (mono x)    = x
headDelta (delta x _) = x

tailDelta : {l : Level} {A : Set l} -> Delta A -> Delta A
tailDelta (mono x)    = mono x
tailDelta (delta _ d) = d

n-tail : {l : Level} {A : Set l} -> Nat -> ((Delta A) -> (Delta A))
n-tail O = id
n-tail (S n) =  tailDelta ∙ (n-tail n)


-- Functor
fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> (Delta A) -> (Delta B)
fmap f (mono x)    = mono  (f x)
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

head-delta-natural-transformation : {l ll : Level} {A : Set l} {B : Set ll}
  -> (f : A -> B) -> (d : Delta A) -> headDelta (fmap f d) ≡ f (headDelta d)
head-delta-natural-transformation f (mono x)    = refl
head-delta-natural-transformation f (delta x d) = refl

n-tail-natural-transformation  : {l ll : Level} {A : Set l} {B : Set ll}
  -> (n : Nat) -> (f : A -> B) -> (d : Delta A) ->  n-tail n (fmap f d) ≡ fmap f (n-tail n d)
n-tail-natural-transformation O f d            = refl
n-tail-natural-transformation (S n) f (mono x) = begin
  n-tail (S n) (fmap f (mono x))  ≡⟨ refl ⟩
  n-tail (S n) (mono (f x))       ≡⟨ tail-delta-to-mono (S n) (f x) ⟩
  (mono (f x))                    ≡⟨ refl ⟩
  fmap f (mono x)                 ≡⟨ cong (\d -> fmap f d) (sym (tail-delta-to-mono (S n) x)) ⟩
  fmap f (n-tail (S n) (mono x))  ∎
n-tail-natural-transformation (S n) f (delta x d) = begin
  n-tail (S n) (fmap f (delta x d))                 ≡⟨ refl ⟩
  n-tail (S n) (delta (f x) (fmap f d))             ≡⟨ cong (\t -> t (delta (f x) (fmap f d))) (sym (n-tail-plus n)) ⟩
  ((n-tail n) ∙ tailDelta) (delta (f x) (fmap f d)) ≡⟨ refl ⟩
  n-tail n (fmap f d)                               ≡⟨ n-tail-natural-transformation n f d ⟩
  fmap f (n-tail n d)                               ≡⟨ refl ⟩
  fmap f (((n-tail n) ∙ tailDelta) (delta x d))     ≡⟨ cong (\t -> fmap f (t (delta x d))) (n-tail-plus n) ⟩
  fmap f (n-tail (S n) (delta x d))                 ∎





