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
            : Set l where
   deltaM : Delta (M A) -> DeltaM M {functorM} {monadM} A


-- DeltaM utils

headDeltaM : {l : Level} {A : Set l}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level} -> Monad {l'} M functorM}
             -> DeltaM M {functorM} {monadM} A -> M A
headDeltaM (deltaM d) = headDelta d


tailDeltaM :  {l : Level} {A : Set l}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level}  -> Monad {l'} M functorM}                                                                 
             -> DeltaM M {functorM} {monadM} A -> DeltaM M {functorM} {monadM} A
tailDeltaM (deltaM d)    = deltaM (tailDelta d)


appendDeltaM : {l : Level} {A : Set l}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level}  -> Monad {l'} M functorM}
             -> DeltaM M {functorM} {monadM} A -> DeltaM M {functorM} {monadM} A -> DeltaM M {functorM} {monadM} A               
appendDeltaM (deltaM d) (deltaM dd) = deltaM (deltaAppend d dd)


checkOut : {l : Level} {A : Set l}
           {M : {l' : Level} -> Set l' -> Set l'}
           {functorM : {l' : Level} -> Functor {l'} M}
           {monadM : {l' : Level} -> Monad {l'} M functorM}
         -> Nat -> DeltaM M {functorM} {monadM} A -> M A
checkOut O     (deltaM (mono x))    = x
checkOut O     (deltaM (delta x _)) = x
checkOut (S n) (deltaM (mono x))    = x
checkOut {l} {A} {M} {functorM} {monadM} (S n) (deltaM (delta _ d)) = checkOut {l} {A} {M} {functorM} {monadM} n (deltaM d)



-- functor definitions
open Functor
deltaM-fmap : {l : Level} {A B : Set l}
              {M : {l' : Level} -> Set l' -> Set l'}
              {functorM : {l' : Level} -> Functor {l'} M}
              {monadM : {l' : Level} -> Monad {l'}  M functorM}
              -> (A -> B) -> DeltaM M {functorM} {monadM} A -> DeltaM M {functorM} {monadM} B
deltaM-fmap {l} {A} {B} {M} {functorM} f (deltaM d) = deltaM (fmap delta-is-functor (fmap functorM f) d)

-- monad definitions
open Monad
deltaM-eta : {l : Level} {A : Set l} {M : {l' : Level} -> Set l' -> Set l'}
                                        {functorM : {l' : Level} -> Functor {l'} M}
                                        {monadM   : {l' : Level}  -> Monad {l'}  M functorM}
            -> A -> (DeltaM M {functorM} {monadM} A)
deltaM-eta {_} {A} {_} {_} {monadM} x = deltaM (mono (eta monadM x))

deltaM-mu : {l : Level} {A : Set l} {M : {l' : Level} -> Set l' -> Set l'}
                                        {functorM : {l' : Level} -> Functor {l'} M}
                                        {monadM   : {l' : Level} -> Monad {l'}  M functorM}
            -> (DeltaM M {functorM} {monadM} (DeltaM M {functorM} {monadM} A)) -> DeltaM M {functorM} {monadM} A
deltaM-mu {l} {A} {M} {functorM} {monadM} (deltaM (mono x))               = deltaM (mono (mu monadM (fmap functorM headDeltaM x)))
deltaM-mu {l} {A} {M} {functorM} {monadM} (deltaM (delta x (mono xx)))    = appendDeltaM (deltaM (mono (bind  monadM x headDeltaM)))
                                                                                         (deltaM-mu (deltaM (mono xx)))
deltaM-mu {l} {A} {M} {functorM} {monadM} (deltaM (delta x (delta xx d))) = appendDeltaM (deltaM (mono (bind {l}  monadM x headDeltaM)))
                                                                                         (deltaM-mu (deltaM  d))
-- original deltaM-mu definitions. but it's cannot termination checking.
-- manually expand nested delta for delete tailDelta in argument to recursive deltaM-mu.
{-
deltaM-mu {l} {A} {M} {functorM} {monadM} (deltaM (delta x d)) =  appendDeltaM (deltaM (mono (bind monadM x headDeltaM)))
                                                                               (deltaM-mu (deltaM (tailDelta d)))
-}

deltaM-bind : {l : Level} {A B : Set l} {M : {l' : Level} -> Set l' -> Set l'} 
                                        {functorM : {l' : Level} -> Functor {l'} M}
                                        {monadM   : {l' : Level} -> Monad {l'} M functorM}
            -> (DeltaM M {functorM} {monadM} A) -> (A -> DeltaM M {functorM} {monadM} B) -> DeltaM M {functorM} {monadM} B
deltaM-bind {l} {A} {B} {M} {functorM} {monadM} d    f = deltaM-mu (deltaM-fmap f d)
