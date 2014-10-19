open import list
open import basic

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module similar where

data Similar {l : Level} (A : Set l) : (Set (suc l)) where
  similar : List String -> A -> List String -> A -> Similar A


-- Functor
fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> (Similar A) -> (Similar B)
fmap f (similar xs x ys y) = similar xs (f x) ys (f y)


-- Monad
mu : {l : Level} {A : Set l} -> Similar (Similar A) -> Similar A
mu (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = similar (lx ++ llx) x (ly ++ lly) y

return : {l : Level} {A : Set l} -> A -> Similar A
return x = similar [] x [] x

returnS : {l : Level} {A : Set l} -> A -> Similar A
returnS x = similar [[ (show x) ]] x [[ (show x) ]] x

returnSS : {l : Level} {A : Set l} -> A -> A -> Similar A
returnSS x y = similar [[ (show x) ]] x [[ (show y) ]] y



-- proofs


-- Functor-laws

-- Functor-law-1 : T(id) = id'
functor-law-1 :  {l : Level} {A : Set l} ->  (s : Similar A) -> (fmap id) s ≡ id s
functor-law-1 (similar lx x ly y) = refl

-- Functor-law-2 : T(f . g) = T(f) . T(g)
functor-law-2 : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                (f : B -> C) -> (g : A -> B) -> (s : Similar A) ->
                (fmap (f ∙ g)) s ≡ ((fmap f) ∙ (fmap g)) s
functor-law-2 f g (similar lx x ly y) = refl



-- Monad-laws

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


--monad-law-2 : mu ∙ fmap return ≡ mu ∙ return ≡ id
monad-law-2-1 : {l : Level} {A : Set l} -> (s : Similar  A) ->
  (mu ∙ fmap return) s ≡ (mu ∙ return) s
monad-law-2-1 (similar lx x ly y) = begin
    similar (lx ++ []) x (ly ++ []) y
  ≡⟨ cong (\left-list -> similar left-list x (ly ++ []) y) (empty-append lx)⟩
    similar lx x (ly ++ []) y
  ≡⟨ cong (\right-list -> similar lx x right-list y) (empty-append ly) ⟩
    similar lx x ly y
  ∎

monad-law-2-2 : {l : Level} {A : Set l } -> (s : Similar A) -> (mu ∙ return) s ≡ id s
monad-law-2-2 (similar lx x ly y) = refl


monad-law-3 : {l : Level} {A B : Set l} (f : A -> B) (x : A) -> (return ∙ f) x ≡ (fmap f ∙ return) x
monad-law-3 f x = refl


monad-law-4 : {l : Level} {A B : Set l} (f : A -> B) (s : Similar (Similar A)) ->
              (mu ∙ fmap (fmap f)) s ≡ (fmap f ∙ mu) s
monad-law-4 f (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = refl