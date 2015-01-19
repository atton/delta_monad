open import Relation.Binary.PropositionalEquality
open import Level
open import basic

module laws where

record Functor {l : Level} (F : Set l -> Set l) : (Set (suc l)) where
  field
    fmap : {A B : Set l} -> (A -> B) -> (F A) -> (F B)
  field
    preserve-id : {A : Set l} (x : F A) → fmap id x ≡ id x
    covariant   : {A B C : Set l} (f : A -> B) -> (g : B -> C) -> (x : F A)
                    -> fmap (g ∙ f) x ≡ ((fmap g) ∙ (fmap f)) x
open Functor



record NaturalTransformation {l : Level} (F G : Set l -> Set l)
                                            (functorF : Functor F)
                                            (functorG : Functor G) : Set (suc l) where
  field
    natural-transformation : {A : Set l}  -> F A -> G A
  field
    commute : ∀ {A B} -> (f : A -> B) -> (x : F A) ->
              natural-transformation (fmap functorF f x) ≡  fmap functorG f (natural-transformation x)
open NaturalTransformation



-- simple Monad definition. without NaturalTransformation (mu, eta) and monad-law with f.
record Monad {l : Level} {A : Set l}
                         (M : {ll : Level} -> Set ll -> Set ll)
                         (functorM : Functor M)
                         : Set (suc l)  where
  field -- category
    mu  :  {A : Set l} -> M (M A) -> M A
    eta :  {A : Set l} -> A -> M A
  field -- haskell
    return : {A : Set l} -> A -> M A
    bind   : {A B : Set l} -> M A -> (A -> (M B)) -> M B
  field -- category laws
    association-law : (x : (M (M (M A)))) -> (mu ∙ (fmap functorM mu)) x ≡ (mu ∙ mu) x
    left-unity-law  : (x : M A) -> (mu  ∙ (fmap functorM eta)) x ≡ id x
    right-unity-law : (x : M A) -> id x ≡ (mu ∙ eta) x

open Monad
