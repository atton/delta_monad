open import Level

open import basic
open import delta
open import delta.functor
open import nat
open import laws

module deltaM where

-- DeltaM definitions

data DeltaM {l : Level} {T : Set l -> Set l} {F : Functor T}
            (M : Monad T F) (A : Set l) : (Nat -> Set l) where
   deltaM : {n : Nat} -> Delta (T A) (S n) -> DeltaM M A (S n)


-- DeltaM utils

unDeltaM : {l : Level} {A : Set l} {n : Nat}
           {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
           (DeltaM M A (S n)) -> Delta (T A) (S n)
unDeltaM (deltaM d) = d



headDeltaM : {l : Level} {A : Set l} {n : Nat}
             {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
             DeltaM M A (S n) -> T A
headDeltaM (deltaM d) = headDelta d



tailDeltaM :  {l : Level} {A : Set l} {n : Nat}
              {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
              DeltaM M A (S (S n)) -> DeltaM M A (S n)
tailDeltaM {_} {n} (deltaM d) = deltaM (tailDelta d)



appendDeltaM : {l : Level} {A : Set l} {n m : Nat}
               {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
               DeltaM M A (S n) -> DeltaM M A (S m) -> DeltaM M A ((S n) + (S m))
appendDeltaM (deltaM d) (deltaM dd) = deltaM (deltaAppend d dd)


dmap : {l : Level} {A B : Set l} {n : Nat}
       {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
       (T A -> B) -> DeltaM M A (S n) -> Delta B (S n)
dmap f (deltaM d) = delta-fmap f d




-- functor definitions
open Functor
deltaM-fmap : {l : Level} {A B : Set l} {n : Nat}
              {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
              (A -> B) -> DeltaM M A (S n) -> DeltaM M B (S n)
deltaM-fmap {l} {A} {B} {n} {M} {functorM} f d = deltaM (fmap delta-is-functor (fmap functorM f) (unDeltaM d))




-- monad definitions
open Monad

deltaM-eta : {l : Level} {A : Set l} {n : Nat}
             {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
             A -> (DeltaM M A (S n))
deltaM-eta {n = n} {M = M} x = deltaM (delta-eta {n = n} (eta M x))



deltaM-mu : {l : Level} {A : Set l} {n : Nat}
            {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
            DeltaM M (DeltaM M A (S n)) (S n) -> DeltaM M A (S n)
deltaM-mu {n = O}   {F = F} {M = M} d = deltaM (mono  (mu M (fmap F headDeltaM (headDeltaM d))))
deltaM-mu {n = S n} {F = F} {M = M} d = deltaM (delta (mu M (fmap F headDeltaM (headDeltaM d)))
                                                      (unDeltaM (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM d)))))
