open import list

module similar where

postulate String : Set
postulate show   : {A : Set} -> A -> String

data Similar (A : Set) : Set where
  similar : List String -> A -> List String -> A -> Similar A


fmap : {A B : Set} -> (A -> B) -> (Similar A) -> (Similar B)
fmap f (similar xs x ys y) = similar xs (f x) ys (f y)


mu : {A : Set} -> Similar (Similar A) -> Similar A
mu (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = similar (lx ++ llx) x (ly ++ lly) y

returnS : {A : Set} -> A -> Similar A
returnS x = similar [[ (show x) ]] x [[ (show x) ]] x

returnSS : {A : Set} -> A -> A -> Similar A
returnSS x y = similar [[ (show x) ]] x [[ (show y) ]] y


