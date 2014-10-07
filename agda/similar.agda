open import list
open import basic
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module similar where

data Similar (A : Set) : Set where
  similar : List String -> A -> List String -> A -> Similar A

fmap : {A B : Set} -> (A -> B) -> (Similar A) -> (Similar B)
fmap f (similar xs x ys y) = similar xs (f x) ys (f y)

mu : {A : Set} -> Similar (Similar A) -> Similar A
mu (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = similar (lx ++ llx) x (ly ++ lly) y

return : {A : Set} -> A -> Similar A
return x = similar [] x [] x

returnS : {A : Set} -> A -> Similar A
returnS x = similar [[ (show x) ]] x [[ (show x) ]] x

returnSS : {A : Set} -> A -> A -> Similar A
returnSS x y = similar [[ (show x) ]] x [[ (show y) ]] y


monad-law-1 : mu ∙ (fmap mu) ≡ mu ∙ mu
monad-law-1 = {!!} 

--monad-law-2 : mu ∙ fmap return ≡ mu ∙ return ≡id
monad-law-2-1 : mu ∙ fmap return ≡ mu ∙ return
monad-law-2-1 = {!!}

monad-law-2-2 : mu ∙ return ≡ id
monad-law-2-2 = {!!}

monad-law-3 : ∀{f} -> return ∙ f ≡ fmap f ∙ return
monad-law-3 = {!!} 

monad-law-4 : ∀{f} -> mu ∙ fmap (fmap f) ≡ fmap f ∙ mu
monad-law-4 = {!!} 
