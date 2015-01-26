open import Level
open import Relation.Binary.PropositionalEquality


open import basic
open import delta
open import laws
open import nat
open import revision



module delta.functor where

-- Functor-laws

-- Functor-law-1 : T(id) = id'
functor-law-1 :  {l : Level} {A : Set l} {n : Rev} ->  (d : Delta A n) -> (delta-fmap id) d ≡ id d
functor-law-1 (mono x)    = refl
functor-law-1 (delta x d) = cong (delta x) (functor-law-1 d)

-- Functor-law-2 : T(f . g) = T(f) . T(g)
functor-law-2 : {l : Level} {n : Rev} {A B C : Set l} -> 
                (f : B -> C) -> (g : A -> B) -> (d : Delta A n) ->
                (delta-fmap (f ∙ g)) d ≡ ((delta-fmap f) ∙ (delta-fmap g)) d
functor-law-2 f g (mono x)    = refl
functor-law-2 f g (delta x d) = cong (delta (f (g x))) (functor-law-2 f g d)

delta-is-functor : {l : Level} {n : Rev} -> Functor {l} (\A -> Delta A n)
delta-is-functor = record {  fmap = delta-fmap ;
                             preserve-id = functor-law-1;
                             covariant  = \f g -> functor-law-2 g f}
