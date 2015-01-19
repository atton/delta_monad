open import Level

open import delta
open import delta.functor
open import nat
open import laws

module deltaM where

-- DeltaM definitions

data DeltaM {l : Level}
            (M : {l' : Level} -> Set l' -> Set l')
            {functorM : {l' : Level} -> Functor {l'} M}
            {monadM : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}
            (A : Set l)
            : Set l where
   deltaM : Delta (M A) -> DeltaM M {functorM} {monadM} A


-- DeltaM utils

headDeltaM : {l : Level} {A : Set l}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}
             -> DeltaM M {functorM} {monadM} A -> M A
headDeltaM (deltaM (mono x))    = x
headDeltaM (deltaM (delta x _)) = x

tailDeltaM :  {l : Level} {A : Set l}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}                                                                 
             -> DeltaM M {functorM} {monadM} A -> DeltaM M {functorM} {monadM} A
tailDeltaM (deltaM (mono x))    = deltaM (mono x)
tailDeltaM (deltaM (delta _ d)) = deltaM d

appendDeltaM : {l : Level} {A : Set l}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}
             -> DeltaM M {functorM} {monadM} A -> DeltaM M {functorM} {monadM} A -> DeltaM M {functorM} {monadM} A               
appendDeltaM (deltaM d) (deltaM dd) = deltaM (deltaAppend d dd)


checkOut : {l : Level} {A : Set l}
           {M : {l' : Level} -> Set l' -> Set l'}
           {functorM : {l' : Level} -> Functor {l'} M}
           {monadM : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}
         -> Nat -> DeltaM M {functorM} {monadM} A -> M A
checkOut O     (deltaM (mono x))    = x
checkOut O     (deltaM (delta x _)) = x
checkOut (S n) (deltaM (mono x))    = x
checkOut {l} {A} {M} {functorM} {monadM} (S n) (deltaM (delta _ d)) = checkOut {l} {A} {M} {functorM} {monadM} n (deltaM d)


open Functor
deltaM-fmap : {l : Level} {A B : Set l}
              {M : {l' : Level} -> Set l' -> Set l'}
              {functorM : {l' : Level} -> Functor {l'} M}
              {monadM : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}
              -> (A -> B) -> DeltaM M {functorM} {monadM} A -> DeltaM M {functorM} {monadM} B
deltaM-fmap {l} {A} {B} {M} {functorM} f (deltaM d) = deltaM (fmap delta-is-functor (fmap functorM f) d)
