open import Level

open import basic
open import delta
open import delta.functor
open import nat
open import laws

module deltaM where

-- DeltaM definitions

data DeltaM {l : Level}
            (M : {l' : Level} -> Set l' -> Set l')
            {functorM : {l' : Level} -> Functor {l'} M}
            {monadM : {l' : Level} {A : Set l'} -> Monad {l'} M functorM}
            (A : Set l)
            : (Nat -> Set l) where
   deltaM : {n : Nat} -> Delta (M A) (S n) -> DeltaM M {functorM} {monadM} A (S n)


-- DeltaM utils

headDeltaM : {l : Level} {A : Set l} {n : Nat}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level} -> Monad {l'} M functorM}
             -> DeltaM M {functorM} {monadM} A (S n) -> M A
headDeltaM (deltaM d) = headDelta d


tailDeltaM :  {l : Level} {A : Set l} {n : Nat}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level}  -> Monad {l'} M functorM}
             -> DeltaM {l} M {functorM} {monadM} A (S (S n)) -> DeltaM M {functorM} {monadM} A (S n)
tailDeltaM {_} {n} (deltaM d) = deltaM (tailDelta d)


appendDeltaM : {l : Level} {A : Set l} {n m : Nat}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level}  -> Monad {l'} M functorM} ->
             DeltaM M {functorM} {monadM} A (S n) -> 
             DeltaM M {functorM} {monadM} A (S m) -> 
             DeltaM M {functorM} {monadM} A ((S n) +  (S m))
appendDeltaM (deltaM d) (deltaM dd) = deltaM (deltaAppend d dd)




-- functor definitions
open Functor
deltaM-fmap : {l : Level} {A B : Set l} {n : Nat}
              {M : {l' : Level} -> Set l' -> Set l'}
              {functorM : {l' : Level} -> Functor {l'} M}
              {monadM : {l' : Level} -> Monad {l'}  M functorM}
              -> (A -> B) -> DeltaM M {functorM} {monadM} A (S n) -> DeltaM M {functorM} {monadM} B (S n)
deltaM-fmap {l} {A} {B} {n} {M} {functorM} f (deltaM d) = deltaM (fmap delta-is-functor (fmap functorM f) d)




-- monad definitions
open Monad

deltaM-eta : {l : Level} {A : Set l} {n : Nat}
                         {M : {l' : Level} -> Set l' -> Set l'}
                         {functorM : {l' : Level} -> Functor {l'} M}
                         {monadM   : {l' : Level}  -> Monad {l'}  M functorM} ->
            A -> (DeltaM M {functorM} {monadM} A (S n))
deltaM-eta {n = n} {monadM = mm} x = deltaM (delta-eta {n = n} (eta mm x))


deltaM-bind : {l : Level} {A B : Set l} 
                          {n : Nat} 
                          {M : {l' : Level} -> Set l' -> Set l'}
                          {functorM : {l' : Level} -> Functor {l'} M}
                          {monadM   : {l' : Level} -> Monad {l'} M functorM} ->
            (DeltaM M {functorM} {monadM} A (S n)) -> 
            (A -> DeltaM M {functorM} {monadM} B (S n)) 
            -> DeltaM M {functorM} {monadM} B (S n)
deltaM-bind {n = O}   {monadM = mm} (deltaM (mono x))    f = deltaM (mono (bind mm x (headDeltaM ∙ f)))
deltaM-bind {n = S n} {monadM = mm} (deltaM (delta x d)) f = appendDeltaM (deltaM (mono (bind mm x (headDeltaM ∙ f))))
                                                                               (deltaM-bind (deltaM d) (tailDeltaM ∙ f))


deltaM-mu : {l : Level} {A : Set l} {n : Nat}
                        {M : {l' : Level} -> Set l' -> Set l'}
                        {functorM : {l' : Level} -> Functor {l'} M}
                        {monadM   : {l' : Level} -> Monad {l'}  M functorM}
            -> (DeltaM M (DeltaM M {functorM} {monadM} A (S n)) (S n)) -> DeltaM M {functorM} {monadM} A (S n)
deltaM-mu d = deltaM-bind d id
