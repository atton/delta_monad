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


-- Monad (Category)
mu : {l : Level} {A : Set l} -> Similar (Similar A) -> Similar A
mu (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = similar (lx ++ llx) x (ly ++ lly) y

eta : {l : Level} {A : Set l} -> A -> Similar A
eta x = similar [] x [] x

returnS : {l : Level} {A : Set l} -> A -> Similar A
returnS x = similar [[ (show x) ]] x [[ (show x) ]] x

returnSS : {l : Level} {A : Set l} -> A -> A -> Similar A
returnSS x y = similar [[ (show x) ]] x [[ (show y) ]] y


-- Monad (Haskell)
return : {l : Level} {A : Set l} -> A -> Similar A
return = eta


_>>=_ : {l ll : Level} {A : Set l} {B : Set ll} ->
        (x : Similar A) -> (f : A -> (Similar B)) -> (Similar B)
x >>= f = mu (fmap f x)



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



-- Monad-laws (Category)

-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (s : Similar (Similar (Similar A))) -> ((mu ∙ (fmap mu)) s) ≡ ((mu ∙ mu) s)
monad-law-1 (similar lx (similar llx (similar lllx x _ _) _ (similar _ _ _ _))
                     ly (similar   _ (similar _ _ _ _)  lly (similar _ _  llly y))) = begin
    similar (lx ++ (llx ++ lllx)) x (ly ++ (lly ++ llly)) y
  ≡⟨ cong (\left-list -> similar left-list x (ly ++ (lly ++ llly)) y) (list-associative lx llx lllx) ⟩
    similar (lx ++ llx ++ lllx) x (ly ++ (lly ++ llly)) y
  ≡⟨ cong (\right-list -> similar (lx ++ llx ++ lllx) x right-list y ) (list-associative ly lly llly) ⟩
    similar (lx ++ llx ++ lllx) x (ly ++ lly ++ llly) y
  ∎


-- monad-law-2 : join . fmap return = join . return = id
-- monad-law-2-1 join . fmap return = join . return
monad-law-2-1 : {l : Level} {A : Set l} -> (s : Similar  A) ->
  (mu ∙ fmap eta) s ≡ (mu ∙ eta) s
monad-law-2-1 (similar lx x ly y) = begin
    similar (lx ++ []) x (ly ++ []) y
  ≡⟨ cong (\left-list -> similar left-list x (ly ++ []) y) (empty-append lx)⟩
    similar lx x (ly ++ []) y
  ≡⟨ cong (\right-list -> similar lx x right-list y) (empty-append ly) ⟩
    similar lx x ly y
  ∎

-- monad-law-2-2 :  join . return = id
monad-law-2-2 : {l : Level} {A : Set l } -> (s : Similar A) -> (mu ∙ eta) s ≡ id s
monad-law-2-2 (similar lx x ly y) = refl

-- monad-law-3 : return . f = fmap f . return
monad-law-3 : {l : Level} {A B : Set l} (f : A -> B) (x : A) -> (eta ∙ f) x ≡ (fmap f ∙ eta) x
monad-law-3 f x = refl

-- monad-law-4 : join . fmap (fmap f) = fmap f . join
monad-law-4 : {l ll : Level} {A : Set l} {B : Set ll} (f : A -> B) (s : Similar (Similar A)) ->
              (mu ∙ fmap (fmap f)) s ≡ (fmap f ∙ mu) s
monad-law-4 f (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = refl


-- Monad-laws (Haskell)
-- monad-law-h-1 : return a >>= k  =  k a
monad-law-h-1 : {l ll : Level} {A : Set l} {B : Set ll} ->
                (a : A) -> (k : A -> (Similar B)) ->
                (return a >>= k)  ≡ (k a)
monad-law-h-1 a k = begin
    return a >>= k
  ≡⟨ refl ⟩
    mu (fmap k (return a))
  ≡⟨ refl ⟩
    mu (return (k a))
  ≡⟨ refl ⟩
    (mu ∙ return) (k a)
  ≡⟨ refl ⟩
    (mu ∙ eta) (k a)
  ≡⟨ (monad-law-2-2 (k a)) ⟩
    id (k a)
  ≡⟨ refl ⟩
    k a
  ∎

-- monad-law-h-2 : m >>= return  =  m
monad-law-h-2 : {l : Level}{A : Set l} -> (m : Similar A) -> (m >>= return)  ≡ m
monad-law-h-2 (similar lx x ly y) = monad-law-2-1 (similar lx x ly y)

-- monad-law-h-3 : m >>= (\x -> k x >>= h)  =  (m >>= k) >>= h
monad-law-h-3 : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                (m : Similar A)  -> (k : A -> (Similar B)) -> (h : B -> (Similar C)) ->
                (m >>= (\x -> k x >>= h)) ≡ ((m >>= k) >>= h)
monad-law-h-3 (similar lx x ly y) k h = begin
    ((similar lx x ly y) >>= (\x -> (k x) >>= h))
  ≡⟨ refl ⟩
    mu (fmap (\x -> k x >>= h) (similar lx x ly y))
  ≡⟨ refl ⟩
    (mu ∙ fmap (\x -> k x >>= h)) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ fmap (\x -> mu (fmap h (k x)))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ fmap (mu ∙ (\x -> fmap h (k x)))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (fmap mu ∙ (fmap (\x -> fmap h (k x))))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (fmap mu)) ((fmap (\x -> fmap h (k x))) (similar lx x ly y))
  ≡⟨ monad-law-1 (((fmap (\x -> fmap h (k x))) (similar lx x ly y))) ⟩
    (mu ∙ mu) ((fmap (\x -> fmap h (k x))) (similar lx x ly y)) 
  ≡⟨ refl ⟩
    (mu ∙ (mu ∙ (fmap (\x -> fmap h (k x))))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (mu ∙ (fmap ((fmap h) ∙ k)))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (mu ∙ ((fmap (fmap h)) ∙ (fmap k)))) (similar lx x ly y)
  ≡⟨ refl ⟩
    (mu ∙ (mu ∙ (fmap (fmap h)))) (fmap k (similar lx x ly y))
  ≡⟨ refl ⟩
    mu ((mu ∙ (fmap (fmap h))) (fmap k (similar lx x ly y)))
  ≡⟨ cong (\fx -> mu fx) (monad-law-4 h (fmap k (similar lx x ly y))) ⟩
    mu (fmap h (mu (similar lx (k x) ly (k y))))
  ≡⟨ refl ⟩
    (mu ∙ fmap h) (mu (fmap k (similar lx x ly y)))
  ≡⟨ refl ⟩
    mu (fmap h (mu (fmap k (similar lx x ly y))))
  ≡⟨ refl ⟩
    (mu (fmap k (similar lx x ly y))) >>= h
  ≡⟨ refl ⟩
    ((similar lx x ly y) >>= k) >>= h
  ∎
