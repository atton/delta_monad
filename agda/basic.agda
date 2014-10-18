open import Level

module basic where

id : {l : Level} {A : Set l} -> A -> A
id x = x

_∙_ : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} -> (B -> C) -> (A -> B) -> (A -> C)
f ∙ g = \x -> f (g x)

postulate String : Set
postulate show   : {A : Set} -> A -> String