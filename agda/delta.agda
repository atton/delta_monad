open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import list
open import basic
open import nat
open import laws

module delta where

data Delta {l : Level} (A : Set l) : (Nat -> (Set l)) where
  mono    : A -> Delta A (S O)
  delta   : {n : Nat} -> A -> Delta A (S n) -> Delta A (S (S n))

deltaAppend : {l : Level} {A : Set l} {n m : Nat} -> Delta A (S n) -> Delta A (S m) -> Delta A ((S n) + (S m))
deltaAppend (mono x) d     = delta x d
deltaAppend (delta x d) ds = delta x (deltaAppend d ds)

headDelta : {l : Level} {A : Set l} {n : Nat} -> Delta A (S n) -> A
headDelta (mono x)    = x
headDelta (delta x _) = x

tailDelta : {l : Level} {A : Set l} {n : Nat} -> Delta A (S (S n)) -> Delta A (S n)
tailDelta (delta _ d) = d



-- Functor
delta-fmap : {l : Level} {A B : Set l} {n : Nat} -> (A -> B) -> (Delta A (S n)) -> (Delta B (S n))
delta-fmap f (mono x)    = mono  (f x)
delta-fmap f (delta x d) = delta (f x) (delta-fmap f d)



-- Monad (Category)
delta-eta : {l : Level} {A : Set l} {n : Nat} -> A -> Delta A (S n)
delta-eta {n = O}     x = mono x
delta-eta {n = (S n)} x = delta x (delta-eta {n = n} x)

delta-mu : {l : Level} {A : Set l} {n : Nat} -> (Delta (Delta A (S n)) (S n)) -> Delta A (S n)
delta-mu (mono x)    = x
delta-mu (delta x d) = delta (headDelta x) (delta-mu (delta-fmap tailDelta d))

delta-bind : {l : Level} {A B : Set l} {n : Nat} -> (Delta A (S n)) -> (A -> Delta B (S n)) -> Delta B (S n)
delta-bind d f = delta-mu (delta-fmap f d)

{-
-- Monad (Haskell)
delta-return : {l : Level} {A : Set l} -> A -> Delta A (S O)
delta-return = delta-eta

_>>=_ : {l : Level} {A B : Set l} {n : Nat} ->
        (x : Delta A n) -> (f : A -> (Delta B n)) -> (Delta B n)
d >>= f = delta-bind d f

-}
