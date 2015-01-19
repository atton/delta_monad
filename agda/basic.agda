open import Level

module basic where

id : {l : Level} {A : Set l} -> A -> A
id x = x

_∙_ : {l : Level} {A B C : Set l} -> (B -> C) -> (A -> B) -> (A -> C)
f ∙ g = \x -> f (g x)

postulate String : Set
postulate show   : {l : Level} {A : Set l} -> A -> String