open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import basic
open import delta
open import laws
open import nat

module delta.functor where

-- Functor-laws

-- Functor-law-1 : T(id) = id'
functor-law-1 :  {l : Level} {A : Set l} {n : Nat} ->  (d : Delta A (S n)) -> (delta-fmap id) d ≡ id d
functor-law-1 (mono x)    = refl
functor-law-1 (delta x d) = cong (delta x) (functor-law-1 d)

-- Functor-law-2 : T(f . g) = T(f) . T(g)
functor-law-2 : {l : Level} {n : Nat} {A B C : Set l} ->
                (f : B -> C) -> (g : A -> B) -> (d : Delta A (S n)) ->
                (delta-fmap (f ∙ g)) d ≡ ((delta-fmap f) ∙ (delta-fmap g)) d
functor-law-2 f g (mono x)    = refl
functor-law-2 f g (delta x d) = cong (delta (f (g x))) (functor-law-2 f g d)


delta-fmap-equiv : {l : Level} {A B : Set l} {n : Nat} {f g : A -> B} 
                   (eq : (x : A) -> f x ≡ g x) -> (d : Delta A (S n)) ->
                   delta-fmap f d ≡ delta-fmap g d
delta-fmap-equiv {l} {A} {B} {O} {f} {g} eq (mono x) = begin
  mono (f x) ≡⟨ cong mono (eq x) ⟩
  mono (g x)
  ∎
delta-fmap-equiv {l} {A} {B} {S n} {f} {g} eq (delta x d) = begin
  delta (f x) (delta-fmap f d) ≡⟨ cong (\de -> delta de (delta-fmap f d)) (eq x) ⟩
  delta (g x) (delta-fmap f d) ≡⟨ cong (\de -> delta (g x) de) (delta-fmap-equiv eq d) ⟩
  delta (g x) (delta-fmap g d)
  ∎



delta-is-functor : {l : Level} {n : Nat} -> Functor {l} (\A -> Delta A (S n))
delta-is-functor = record { fmap       = delta-fmap
                          ;preserve-id = functor-law-1
                          ; covariant  = \f g -> functor-law-2 g f
                          ; fmap-equiv = delta-fmap-equiv
                          }
