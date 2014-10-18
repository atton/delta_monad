open import list
open import basic

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module similar where

data Similar {l : Level} (A : Set l) : (Set (suc l)) where
  similar : List String -> A -> List String -> A -> Similar A

fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> (Similar A) -> (Similar B)
fmap f (similar xs x ys y) = similar xs (f x) ys (f y)

mu : {l : Level} {A : Set l} -> Similar (Similar A) -> Similar A
mu (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = similar (lx ++ llx) x (ly ++ lly) y

return : {A : Set} -> A -> Similar A
return x = similar [] x [] x

returnS : {A : Set} -> A -> Similar A
returnS x = similar [[ (show x) ]] x [[ (show x) ]] x

returnSS : {A : Set} -> A -> A -> Similar A
returnSS x y = similar [[ (show x) ]] x [[ (show y) ]] y


--monad-law-1 : mu ∙ (fmap mu) ≡ mu ∙ mu
monad-law-1 : {l : Level} {A : Set l} -> (s : Similar (Similar (Similar A))) -> ((mu ∙ (fmap mu)) s) ≡ ((mu ∙ mu) s)
monad-law-1 (similar lx (similar llx (similar lllx x _ _) _ (similar _ _ _ _)) 
                     ly (similar   _ (similar _ _ _ _)  lly (similar _ _  llly y))) = begin
    similar (lx ++ (llx ++ lllx)) x (ly ++ (lly ++ llly)) y
  ≡⟨ cong (\left-list -> similar left-list x (ly ++ (lly ++ llly)) y) (list-associative lx llx lllx) ⟩
    similar (lx ++ llx ++ lllx) x (ly ++ (lly ++ llly)) y
  ≡⟨ cong (\right-list -> similar (lx ++ llx ++ lllx) x right-list y ) (list-associative ly lly llly) ⟩
    similar (lx ++ llx ++ lllx) x (ly ++ lly ++ llly) y
  ∎

{-
--monad-law-2 : mu ∙ fmap return ≡ mu ∙ return ≡id
monad-law-2-1 : mu ∙ fmap return ≡ mu ∙ return
monad-law-2-1 = {!!}

monad-law-2-2 : mu ∙ return ≡ id
monad-law-2-2 = {!!}

monad-law-3 : ∀{f} -> return ∙ f ≡ fmap f ∙ return
monad-law-3 = {!!}

monad-law-4 : ∀{f} -> mu ∙ fmap (fmap f) ≡ fmap f ∙ mu
monad-law-4 = {!!}
-}
