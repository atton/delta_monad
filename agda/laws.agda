open import Relation.Binary.PropositionalEquality
open import Level
open import basic

module laws where

record Functor {l : Level} (F : Set l -> Set l) : Set (suc l) where
  field
    fmap : {A B : Set l} -> (A -> B) -> (F A) -> (F B)
  field
    preserve-id : {A : Set l} (x : F A) → fmap id x ≡ id x
    covariant   : {A B C : Set l} (f : A -> B) -> (g : B -> C) -> (x : F A)
                    -> fmap (g ∙ f) x ≡ ((fmap g) ∙ (fmap f)) x
open Functor

record NaturalTransformation {l : Level} (F G : Set l -> Set l)
                                         {fmapF : {A B : Set l} -> (A -> B) -> (F A) -> (F B)}
                                         {fmapG : {A B : Set l} -> (A -> B) -> (G A) -> (G B)}
                                         (natural-transformation : {A : Set l}  -> F A -> G A)
                             : Set (suc l) where
  field
    commute : {A B : Set l} -> (f : A -> B) -> (x : F A) ->
              natural-transformation (fmapF f x) ≡  fmapG f (natural-transformation x)
open NaturalTransformation





-- Categorical Monad definition. without haskell-laws (bind)
record Monad {l : Level} (T : Set l -> Set l) (F : Functor T) : Set (suc l)  where
  field -- category
    mu  :  {A : Set l} -> T (T A) -> T A
    eta :  {A : Set l} -> A -> T A
  field -- natural transformations
    eta-is-nt : {A B : Set l} -> (f : A -> B) -> (x : A)       -> (eta ∙ f) x ≡ fmap F f (eta x)
    mu-is-nt  : {A B : Set l} -> (f : A -> B) -> (x : T (T A)) -> mu (fmap F (fmap F f) x) ≡ fmap F f (mu x)
  field -- category laws
    association-law : {A : Set l} -> (x : (T (T (T A)))) -> (mu ∙ (fmap F mu))  x ≡ (mu ∙ mu) x
    left-unity-law  : {A : Set l} -> (x : T A)           -> (mu ∙ (fmap F eta)) x ≡ id x
    right-unity-law : {A : Set l} -> (x : T A)           -> id x ≡ (mu ∙ eta) x


open Monad
