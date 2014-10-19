module list where

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

infixr 40 _::_
data  List {l : Level} (A : Set l) : (Set l)where
   [] : List A
   _::_ : A -> List A -> List A


infixl 30 _++_
_++_ : {l : Level} {A : Set l} -> List A -> List A -> List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

[[_]] : {l : Level} {A : Set l} -> A -> List A
[[ x ]] = x :: []


empty-append : {l : Level} {A : Set l} -> (xs : List A) -> xs ++ [] ≡ [] ++ xs
empty-append [] = refl
empty-append (x :: xs) = begin
    x :: (xs ++ [])
  ≡⟨ cong (_::_ x) (empty-append xs) ⟩
    x :: xs
  ∎


list-associative : {l : Level} {A : Set l} -> (a b c : List A) -> (a ++ (b ++ c)) ≡ ((a ++ b) ++ c)
list-associative [] b c = refl
list-associative (x :: a) b c = cong (_::_ x) (list-associative a b c)