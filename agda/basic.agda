module basic where

id : {A : Set} -> A -> A
id x = x

_∙_ : {A B C : Set} -> (A -> B) -> (B -> C) -> (A -> C)
f ∙ g = \x -> g (f x)

postulate String : Set
postulate show   : {A : Set} -> A -> String