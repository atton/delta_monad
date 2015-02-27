open import Function
open import Level

module delta where

data Delta {l : Level} (A : Set l) {B : Set l} : Set l where
  delta : A -> B -> Delta A {B}

fst : {l : Level} {A B : Set l} -> Delta A {B} -> A
fst (delta x _) = x

eta : {l : Level} {A B : Set l} -> A -> {x' : B} -> Delta A {B}
eta x {x'} = delta x x'


bind : {l : Level} {A A' B B' X : Set l} -> {f' : A' -> B'}
  -> Delta A {A'} -> (A -> Delta B {X}) -> Delta B {B'}
bind {f' = f'} (delta x x') f = delta (fst (f x))  (f' x')

mu : {l : Level} {A A' : Set l} -> Delta (Delta A {A'}) {A'} -> Delta A
mu d = bind {f' = id} d id

program : {l : Level} {A A' B B' C C' X : Set l} -> (x : Delta A {A'}) 
  (f : A -> Delta B {X} ) -> {f' : A' -> B'} ->  (g : B -> Delta C {X}) -> {g' : B' -> C'} -> Delta C {C'}
program x f {f'} g {g'} = bind {f' = g'} (bind {f' = f'} x f) g