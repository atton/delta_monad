open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import basic
open import delta
open import delta.functor
open import deltaM
open import deltaM.functor
open import laws

module deltaM.monad where
open Functor
open NaturalTransformation
open Monad


postulate deltaM-mu-is-natural-transformation : {l : Level} {A : Set l}
                                                  {M : {l' : Level} -> Set l' -> Set l'} -> 
                                                  {functorM :  {l' : Level} -> Functor {l'}  M}
                                                  {monadM   : {l' : Level} {A : Set l'} -> Monad {l'} {A} M (functorM ) } ->
                                                  NaturalTransformation (\A -> DeltaM M (DeltaM M A)) (\A -> DeltaM M A)
                                                                        {deltaM-fmap ∙ deltaM-fmap} {deltaM-fmap {l}}
                                                  (deltaM-mu {_} {_} {M} {functorM} {monadM})

headDeltaM-commute : {l : Level} {A B : Set l}
                                 {M : {l' : Level} -> Set l' -> Set l'} -> 
                                 {functorM :  {l' : Level}  -> Functor {l'}  M} ->
                                 {monadM   : {l' : Level} {A : Set l'} -> Monad {l'} {A} M (functorM ) } ->
                                 (f : A -> B) -> (x : DeltaM M {functorM} {monadM} A) -> 
                    headDeltaM (deltaM-fmap f x) ≡ fmap functorM  f (headDeltaM x)
headDeltaM-commute f (deltaM (mono x))    = refl
headDeltaM-commute f (deltaM (delta x d)) = refl


headDeltaM-is-natural-transformation : {l : Level} {A : Set l}
                                                  {M : {l' : Level} -> Set l' -> Set l'} ->
                                                  {functorM :  {l' : Level} -> Functor {l'} M}
                                                  {monadM   : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM } ->
                                                  NaturalTransformation {l} (\A -> DeltaM M {functorM} {monadM} A) M
                                                                            {\f d → deltaM (mono (headDeltaM (deltaM-fmap f d)))} {fmap functorM} headDeltaM
--                                                                      {deltaM-fmap} {fmap (functorM {l} {A})} headDeltaM
headDeltaM-is-natural-transformation = record { commute = headDeltaM-commute }



deltaM-association-law : {l : Level} {A : Set l}
                              {M : {l' : Level} -> Set l' -> Set l'}
                              (functorM : {l' : Level}  -> Functor {l'} M)
                              (monadM   : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM)
                  -> (d : DeltaM M (DeltaM M (DeltaM M {functorM} {monadM} A)))
                  -> ((deltaM-mu ∙ (deltaM-fmap deltaM-mu)) d) ≡ ((deltaM-mu ∙ deltaM-mu) d)
deltaM-association-law functorM monadM (deltaM x) = {!!} 
{-
 begin
  (deltaM-mu ∙ deltaM-fmap deltaM-mu) d ≡⟨ refl ⟩
  deltaM-mu (deltaM-fmap deltaM-mu d)   ≡⟨ {!!} ⟩
  deltaM-mu (deltaM-mu d)               ≡⟨ refl ⟩
  (deltaM-mu ∙ deltaM-mu) d
  ∎
-}
{-
deltaM-association-law functorM monadM (deltaM (mono x))    = begin
  (deltaM-mu ∙ deltaM-fmap deltaM-mu) (deltaM (mono x))                           ≡⟨ refl ⟩
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (mono x)))                             ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta-fmap (fmap functorM deltaM-mu) (mono x)))              ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (fmap functorM deltaM-mu x)))                           ≡⟨ refl ⟩
  deltaM-bind (deltaM (mono (fmap functorM deltaM-mu x))) id                      ≡⟨ refl ⟩
  deltaM (mono (bind monadM (fmap functorM deltaM-mu x) (headDeltaM ∙ id)))       ≡⟨ refl ⟩
  deltaM (mono (bind monadM (fmap functorM deltaM-mu x) headDeltaM))              ≡⟨ {!!} ⟩
  deltaM (mono (bind monadM (bind monadM x headDeltaM) headDeltaM))               ≡⟨ refl ⟩
  deltaM (mono (bind monadM (bind monadM x (headDeltaM ∙ id)) (headDeltaM ∙ id))) ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (bind monadM x (headDeltaM ∙ id))))                     ≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (mono x)))                                         ≡⟨ refl ⟩
  (deltaM-mu ∙ deltaM-mu) (deltaM (mono x))                                       ∎
deltaM-association-law functorM monadM (deltaM (delta x d)) = {!!}
-}

{-

nya : {l : Level} {A B C : Set l} ->
                       {M : {l' : Level} -> Set l' -> Set l'}
                       {functorM : {l' : Level} -> Functor {l'} M }
                       {monadM : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}
                       (m : DeltaM M {functorM} {monadM}  A)  -> (f : A -> (DeltaM M {functorM} {monadM} B)) -> (g : B -> (DeltaM M C)) ->
                       (x : M A) ->
  (deltaM (fmap delta-is-functor (\x -> bind {l} {A} monadM x (headDeltaM ∙ (\x -> deltaM-bind (f x) g))) (mono x))) ≡
  (deltaM-bind (deltaM (fmap delta-is-functor (\x -> (bind {l} {A} monadM x (headDeltaM ∙ f))) (mono x))) g)
nya = {!!}

deltaM-monad-law-h-3 : {l : Level} {A B C : Set l} ->
                       {M : {l' : Level} -> Set l' -> Set l'}
                       {functorM : {l' : Level} -> Functor {l'} M }
                       {monadM : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}
                       (m : DeltaM M {functorM} {monadM}  A)  -> (f : A -> (DeltaM M  B)) -> (g : B -> (DeltaM M C)) ->
                       (deltaM-bind m (\x -> deltaM-bind (f x) g)) ≡ (deltaM-bind (deltaM-bind m f) g)
{-
deltaM-monad-law-h-3 {l} {A} {B} {C} {M} {functorM} {monadM} (deltaM (mono x)) f g    = begin
  (deltaM-bind (deltaM (mono x)) (\x -> deltaM-bind (f x) g))                         ≡⟨ refl ⟩

  (deltaM (mono (bind {l} {A} monadM x (headDeltaM ∙ (\x -> deltaM-bind (f x) g)))))  ≡⟨ {!!} ⟩
  (deltaM-bind (deltaM (fmap delta-is-functor (\x -> (bind {l} {A} monadM x (headDeltaM ∙ f))) (mono x))) g) ≡⟨ refl ⟩
  (deltaM-bind (deltaM (mono (bind {l} {A} monadM x (headDeltaM ∙ f)))) g) ≡⟨ refl ⟩
  (deltaM-bind (deltaM-bind (deltaM (mono x)) f) g) ∎
-}

deltaM-monad-law-h-3 {l} {A} {B} {C} {M} {functorM} {monadM} (deltaM (mono x)) f g    = begin
  (deltaM-bind (deltaM (mono x)) (\x -> deltaM-bind (f x) g))                         ≡⟨ refl ⟩
  (deltaM (mono (bind {l} {A} monadM x (headDeltaM ∙ (\x -> deltaM-bind (f x) g)))))  ≡⟨ {!!} ⟩
--  (deltaM (fmap delta-is-functor (\x -> bind {l} {A} monadM x (headDeltaM ∙ (\x -> deltaM-bind (f x) g))) (mono x))) ≡⟨ {!!} ⟩
  deltaM (mono (bind {l} {B} monadM (bind {_} {A} monadM x (headDeltaM ∙ f)) (headDeltaM ∙ g))) ≡⟨ {!!} ⟩
  deltaM (mono (bind {l} {B} monadM (bind {_} {A} monadM x (headDeltaM ∙ f)) (headDeltaM ∙ g))) ≡⟨ {!!} ⟩
  (deltaM-bind (deltaM (mono (bind {l} {A} monadM x (headDeltaM ∙ f)))) g) ≡⟨ refl ⟩
  (deltaM-bind (deltaM-bind (deltaM (mono x)) f) g)
  ∎
deltaM-monad-law-h-3 (deltaM (delta x d)) f g = {!!}
{-
 begin
  (deltaM-bind m (\x -> deltaM-bind (f x) g)) ≡⟨ {!!} ⟩
  (deltaM-bind (deltaM-bind m f) g)
  ∎
-}
-}
