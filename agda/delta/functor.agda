open import delta
open import basic
open import laws

open import Level
open import Relation.Binary.PropositionalEquality


module delta.functor where

-- Functor-laws

-- Functor-law-1 : T(id) = id'
functor-law-1 :  {l : Level} {A : Set l} ->  (d : Delta A) -> (delta-fmap id) d ≡ id d
functor-law-1 (mono x)    = refl
functor-law-1 (delta x d) = cong (delta x) (functor-law-1 d)

-- Functor-law-2 : T(f . g) = T(f) . T(g)
functor-law-2 : {l : Level} {A B C : Set l} -> 
                (f : B -> C) -> (g : A -> B) -> (d : Delta A) ->
                (delta-fmap (f ∙ g)) d ≡ ((delta-fmap f) ∙ (delta-fmap g)) d
functor-law-2 f g (mono x)    = refl
functor-law-2 f g (delta x d) = cong (delta (f (g x))) (functor-law-2 f g d)

delta-is-functor : {l : Level} -> Functor (Delta {l})
delta-is-functor = record {  fmap = delta-fmap ;
                             preserve-id = functor-law-1;
                             covariant  = \f g -> functor-law-2 g f}
