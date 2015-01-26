open import Level

open import basic
open import delta
open import delta.functor
open import nat
open import revision
open import laws

module deltaM where

-- DeltaM definitions

data DeltaM {l : Level}
            (M : {l' : Level} -> Set l' -> Set l')
            {functorM : {l' : Level} -> Functor {l'} M}
            {monadM : {l' : Level} {A : Set l'} -> Monad {l'} M functorM}
            (A : Set l)
            : (Rev -> Set l) where
   deltaM : {v : Rev} -> Delta (M A) v -> DeltaM M {functorM} {monadM} A v


-- DeltaM utils

headDeltaM : {l : Level} {A : Set l} {v : Rev}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level} -> Monad {l'} M functorM}
             -> DeltaM M {functorM} {monadM} A v -> M A
headDeltaM (deltaM d) = headDelta d


tailDeltaM :  {l : Level} {A : Set l} {v : Rev}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level}  -> Monad {l'} M functorM}
             -> DeltaM {l} M {functorM} {monadM} A (commit v) -> DeltaM M {functorM} {monadM} A v
tailDeltaM {_} {n} (deltaM d) = deltaM (tailDelta d)


appendDeltaM : {l : Level} {A : Set l} {n m : Rev}
             {M : {l' : Level} -> Set l' -> Set l'}
             {functorM : {l' : Level} -> Functor {l'} M}
             {monadM : {l' : Level}  -> Monad {l'} M functorM}
             -> DeltaM M {functorM} {monadM} A  n -> DeltaM M {functorM} {monadM} A m -> DeltaM M {functorM} {monadM} A (merge n m)
appendDeltaM (deltaM d) (deltaM dd) = deltaM (deltaAppend d dd)




-- functor definitions
open Functor
deltaM-fmap : {l : Level} {A B : Set l} {n : Rev}
              {M : {l' : Level} -> Set l' -> Set l'}
              {functorM : {l' : Level} -> Functor {l'} M}
              {monadM : {l' : Level} -> Monad {l'}  M functorM}
              -> (A -> B) -> DeltaM M {functorM} {monadM} A n -> DeltaM M {functorM} {monadM} B n
deltaM-fmap {l} {A} {B} {n} {M} {functorM} f (deltaM d) = deltaM (fmap delta-is-functor (fmap functorM f) d)




-- monad definitions
open Monad

deltaM-eta : {l : Level} {A : Set l} {v : Rev}
                         {M : {l' : Level} -> Set l' -> Set l'}
                         {functorM : {l' : Level} -> Functor {l'} M}
                         {monadM   : {l' : Level}  -> Monad {l'}  M functorM}
            -> A -> (DeltaM M {functorM} {monadM} A v)
deltaM-eta {v = init} {monadM = mm} x = deltaM (mono (eta mm x))
deltaM-eta {v = (commit v)} {monadM = mm} x = appendDeltaM (deltaM (mono (eta mm x)))
                                                           (deltaM-eta {v = v} x)


deltaM-bind : {l : Level} {A B : Set l} {v : Rev} 
                                        {M : {l' : Level} -> Set l' -> Set l'}
                                        {functorM : {l' : Level} -> Functor {l'} M}
                                        {monadM   : {l' : Level} -> Monad {l'} M functorM}
            -> (DeltaM M {functorM} {monadM} A v) -> (A -> DeltaM M {functorM} {monadM} B v) -> DeltaM M {functorM} {monadM} B v
deltaM-bind {v = init}     {monadM = mm} (deltaM (mono x))    f = deltaM (mono (bind mm x (headDeltaM ∙ f)))
deltaM-bind {v = commit v} {monadM = mm} (deltaM (delta x d)) f = appendDeltaM (deltaM (mono (bind mm x (headDeltaM ∙ f))))
                                                                               (deltaM-bind (deltaM d) (tailDeltaM ∙ f))


deltaM-mu : {l : Level} {A : Set l} {v : Rev}
                        {M : {l' : Level} -> Set l' -> Set l'}
                        {functorM : {l' : Level} -> Functor {l'} M}
                        {monadM   : {l' : Level} -> Monad {l'}  M functorM}
            -> (DeltaM M {functorM} {monadM} (DeltaM M {functorM} {monadM} A v) v) -> DeltaM M {functorM} {monadM} A v
deltaM-mu d = deltaM-bind d id
