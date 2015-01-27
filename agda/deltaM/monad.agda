open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import basic
open import delta
open import delta.functor
open import deltaM
open import deltaM.functor
open import nat
open import laws

module deltaM.monad where
open Functor
open NaturalTransformation
open Monad


headDeltaM-commute : {l : Level} {A B : Set l} {n : Nat}
                                 {M : {l' : Level} -> Set l' -> Set l'} -> 
                                 {functorM :  {l' : Level}  -> Functor {l'}  M} ->
                                 {monadM   : {l' : Level} -> Monad {l'} M (functorM ) } ->
                                 (f : A -> B) -> (x : DeltaM M {functorM} {monadM} A n) -> 
                    headDeltaM (deltaM-fmap f x) ≡ fmap functorM  f (headDeltaM x)
headDeltaM-commute f (deltaM (mono x))    = refl
headDeltaM-commute f (deltaM (delta x d)) = refl


{-
headDeltaM-is-natural-transformation : {l : Level} {A : Set l} {n : Nat}
                                       {M : {l' : Level} -> Set l' -> Set l'} ->
                                       {functorM :  {l' : Level} -> Functor {l'} M}
                                       {monadM   : {l' : Level} -> Monad {l'} M functorM } ->
                                       NaturalTransformation {l} (\A -> DeltaM M {functorM} {monadM} A n) M
                                                                 {\f d → deltaM (mono (headDeltaM (deltaM-fmap f d)))}
                                                                 {fmap functorM} headDeltaM

headDeltaM-is-natural-transformation = record { commute = headDeltaM-commute }
-}


deltaM-right-unity-law : {l : Level} {A : Set l} 
                         {M : {l' : Level} -> Set l' -> Set l'}
                         (functorM : {l' : Level} -> Functor {l'} M)
                         (monadM   : {l' : Level} -> Monad {l'} M functorM)
                         (d : DeltaM M {functorM} {monadM} A (S O)) -> 
                              (deltaM-mu ∙ deltaM-eta) d ≡ id d
deltaM-right-unity-law {l} {A} {M} functorM monadM (deltaM (mono x))    = begin
  (deltaM-mu ∙ deltaM-eta) (deltaM (mono x))                ≡⟨ refl ⟩
  deltaM-mu (deltaM-eta (deltaM (mono x)))                  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (eta monadM (deltaM (mono x)))))  ≡⟨ refl ⟩
  deltaM (mono (mu monadM (fmap functorM (headDeltaM {l} {A} {S O} {M}) (eta monadM (deltaM (mono x))))))
  ≡⟨ cong (\de -> deltaM (mono (mu monadM (de)))) (sym (eta-is-nt monadM headDeltaM (deltaM (mono x)))) ⟩
  deltaM (mono (mu monadM (eta monadM (headDeltaM {l} {A} {S O} {M} {functorM} {monadM} (deltaM (mono x))))))
  ≡⟨ refl ⟩
  deltaM (mono (mu monadM (eta monadM x))) 
  ≡⟨ cong (\de -> deltaM (mono de)) (sym (right-unity-law monadM x ) )⟩
  deltaM (mono x)
  ≡⟨ refl ⟩
  id (deltaM (mono x))
  ∎
deltaM-right-unity-law functorM monadM (deltaM (delta x ()))
-- cannot apply (mu ∙ eta) for over 2 version delta.


{-
deltaM-left-unity-law : {l : Level} {A : Set l} 
                        {M : {l' : Level} -> Set l' -> Set l'}
                        (functorM : {l' : Level} -> Functor {l'} M)
                        (monadM   : {l' : Level} -> Monad {l'} M functorM)
                        (d : DeltaM M {functorM} {monadM} A (S O)) -> 
                              (deltaM-mu ∙ (deltaM-fmap deltaM-eta)) d ≡ id d
deltaM-left-unity-law functorM monadM (deltaM (mono x)) = begin
   (deltaM-mu ∙ deltaM-fmap deltaM-eta) (deltaM (mono x)) ≡⟨ refl ⟩
   deltaM-mu (deltaM-fmap deltaM-eta (deltaM (mono x)))   ≡⟨ refl ⟩
   deltaM-mu (deltaM (mono (fmap functorM deltaM-eta x))) ≡⟨ refl ⟩
   deltaM (mono (mu monadM (fmap functorM headDeltaM (fmap functorM deltaM-eta x)))) ≡⟨ {!!} ⟩
   deltaM (mono (mu monadM (fmap functorM headDeltaM (fmap functorM deltaM-eta x)))) ≡⟨ {!!} ⟩

   id (deltaM (mono x))
   ∎
deltaM-left-unity-law functorM monadM (deltaM (delta x ()))
-}

deltaM-is-monad : {l : Level} {A : Set l} {n : Nat}
                              {M : {l' : Level} -> Set l' -> Set l'}
                              (functorM : {l' : Level}  -> Functor {l'} M)
                              (monadM   : {l' : Level}-> Monad {l'}  M functorM) ->
               Monad {l} (\A -> DeltaM M {functorM} {monadM} A n) deltaM-is-functor
deltaM-is-monad functorM monadM = record
                                    { mu = deltaM-mu;
                                      eta = deltaM-eta;
                                    return = {!!};
                                    bind = {!!};
                                    association-law = {!!};
                                    left-unity-law = {!!};
                                    right-unity-law = {!!};
                                    eta-is-nt = {!!}
                                    }






{-
deltaM-association-law : {l : Level} {A : Set l}
                              {M : {l' : Level} -> Set l' -> Set l'}
                              (functorM : {l' : Level}  -> Functor {l'} M)
                              (monadM   : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM)
                  -> (d : DeltaM M (DeltaM M (DeltaM M {functorM} {monadM} A)))
                  -> ((deltaM-mu ∙ (deltaM-fmap deltaM-mu)) d) ≡ ((deltaM-mu ∙ deltaM-mu) d)
deltaM-association-law functorM monadM (deltaM (mono x))    = begin
  (deltaM-mu ∙ deltaM-fmap deltaM-mu) (deltaM (mono x))                           ≡⟨ refl ⟩
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (mono x)))                             ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta-fmap (fmap functorM deltaM-mu) (mono x)))              ≡⟨ {!!} ⟩
  deltaM-mu (deltaM (mono (bind monadM x headDeltaM)))                            ≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (mono x)))                                         ≡⟨ refl ⟩
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