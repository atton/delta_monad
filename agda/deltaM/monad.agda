open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import basic
open import delta
open import delta.functor
open import delta.monad
open import deltaM
open import deltaM.functor
open import nat
open import laws

module deltaM.monad where
open Functor
open NaturalTransformation
open Monad



postulate  deltaM-right-unity-law : {l : Level} {A : Set l}
                         {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM} {n : Nat}
                         (d : DeltaM M {functorM} {monadM} A (S n)) -> (deltaM-mu ∙ deltaM-eta) d ≡ id d
{-
deltaM-right-unity-law {l} {A} {M} {fm} {mm} {O} (deltaM (mono x)) = begin
  deltaM-mu (deltaM-eta (deltaM (mono x)))             ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (eta mm (deltaM (mono x))))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (headDeltaM {M = M})(eta mm (deltaM (mono x))))))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (sym (eta-is-nt mm headDeltaM (deltaM (mono x)) )) ⟩
  deltaM (mono (mu mm (eta mm ((headDeltaM {l} {A} {O} {M} {fm} {mm}) (deltaM (mono x)))))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (eta mm x))) ≡⟨ cong (\de -> deltaM (mono de)) (sym (right-unity-law mm x)) ⟩
  deltaM (mono x)
  ∎
deltaM-right-unity-law {l} {A} {M} {fm} {mm} {S n} (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-eta (deltaM (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (eta mm (deltaM (delta x d))) (delta-eta (eta mm (deltaM (delta x d))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm (headDeltaM {monadM = mm}) (eta mm (deltaM (delta x d)))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono (mu mm de)))
                                (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d))))))))
           (sym (eta-is-nt mm headDeltaM (deltaM (delta x d)))) ⟩
  appendDeltaM (deltaM (mono (mu mm (eta mm ((headDeltaM {monadM = mm}) (deltaM (delta x d)))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (eta mm x))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono de)) (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d))))))))
           (sym (right-unity-law mm x)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM de))) (sym (eta-is-nt delta-is-monad (fmap fm tailDeltaM) (eta mm (deltaM (delta x d))))) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-eta (fmap fm tailDeltaM (eta mm (deltaM (delta x d)))))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-eta de)))) (sym (eta-is-nt mm tailDeltaM (deltaM (delta x d)))) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-eta (eta mm (tailDeltaM (deltaM (delta x d)))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-eta (eta mm (deltaM d)))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-eta (deltaM d)))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) de) (deltaM-right-unity-law (deltaM d)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM d)
  ≡⟨ refl ⟩
  deltaM (delta x d)
  ∎
-}


fmap-headDeltaM-with-deltaM-eta : {l : Level} {A : Set l} {n : Nat}
                                  {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM}
  (x : M A) ->  (fmap functorM ((headDeltaM {l} {A} {n} {M} {functorM} {monadM}) ∙ deltaM-eta) x) ≡ fmap functorM (eta monadM) x
fmap-headDeltaM-with-deltaM-eta {l} {A} {O} {M} {fm} {mm}    x = refl
fmap-headDeltaM-with-deltaM-eta {l} {A} {S n} {M} {fm} {mm} x  = refl

fmap-tailDeltaM-with-deltaM-eta : {l : Level} {A : Set l} {n : Nat}
                   {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM}
                   (d : DeltaM M {functorM} {monadM} A (S n)) ->
       deltaM-fmap ((tailDeltaM {n = n} {monadM = monadM} )  ∙ deltaM-eta) d ≡ deltaM-fmap (deltaM-eta) d
fmap-tailDeltaM-with-deltaM-eta {n = O} d = refl
fmap-tailDeltaM-with-deltaM-eta {n = S n} d = refl



deltaM-left-unity-law : {l : Level} {A : Set l}
                        {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM}
                        {n : Nat}
                        (d : DeltaM M {functorM} {monadM} A (S n)) ->
                              (deltaM-mu ∙ (deltaM-fmap deltaM-eta)) d ≡ id d
deltaM-left-unity-law {l} {A} {M} {fm} {mm} {O} (deltaM (mono x))      = begin
  deltaM-mu (deltaM-fmap deltaM-eta (deltaM (mono x)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta-fmap (fmap fm deltaM-eta) (mono x)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (fmap fm deltaM-eta x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (headDeltaM {l} {A} {O} {M}) (fmap fm deltaM-eta x))))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (sym (covariant fm deltaM-eta headDeltaM x)) ⟩
  deltaM (mono (mu mm (fmap fm ((headDeltaM {l} {A} {O} {M} {fm} {mm}) ∙ deltaM-eta) x)))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (fmap-headDeltaM-with-deltaM-eta {l} {A} {O} {M} {fm} {mm} x) ⟩
  deltaM (mono (mu mm (fmap fm (eta mm) x)))
  ≡⟨ cong (\de -> deltaM (mono de)) (left-unity-law mm x) ⟩
  deltaM (mono x)
  ∎
deltaM-left-unity-law {l} {A} {M} {fm} {mm} {S n} (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-fmap deltaM-eta (deltaM (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta-fmap (fmap fm deltaM-eta) (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (fmap fm deltaM-eta x) (delta-fmap (fmap fm deltaM-eta) d)))
  ≡⟨ refl  ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm (headDeltaM {l} {A} {S n} {M} {fm} {mm}) (fmap fm deltaM-eta x)))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono (mu mm de)))
                                (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d)))))
           (sym (covariant fm deltaM-eta headDeltaM x)) ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm ((headDeltaM {l} {A} {S n} {M} {fm} {mm}) ∙ deltaM-eta) x))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono (mu mm de)))
                                (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d)))))
           (fmap-headDeltaM-with-deltaM-eta {l} {A} {S n} {M} {fm} {mm} x) ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm (eta mm) x))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))

  ≡⟨ cong (\de -> (appendDeltaM (deltaM (mono de)) (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))))
           (left-unity-law mm x) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap (tailDeltaM {n = n})(deltaM-fmap deltaM-eta (deltaM d))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) (deltaM-mu de)) (sym (covariant deltaM-is-functor deltaM-eta tailDeltaM (deltaM d))) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap ((tailDeltaM {n = n}) ∙ deltaM-eta) (deltaM d)))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) (deltaM-mu de)) (fmap-tailDeltaM-with-deltaM-eta (deltaM d)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap deltaM-eta (deltaM d)))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) de) (deltaM-left-unity-law (deltaM d)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM d)
  ≡⟨ refl ⟩
  deltaM (delta x d)
  ∎



deltaM-is-monad : {l : Level} {A : Set l} {n : Nat}
                              {M : Set l -> Set l}
                              (functorM : Functor M)
                              (monadM   : Monad M functorM) ->
               Monad {l} (\A -> DeltaM M {functorM} {monadM} A (S n)) (deltaM-is-functor {l} {n})
deltaM-is-monad functorM monadM = record
                                    { mu     = deltaM-mu;
                                      eta    = deltaM-eta;
                                      return = deltaM-eta;
                                      bind   = deltaM-bind;
                                      association-law = {!!};
                                      left-unity-law  = deltaM-left-unity-law;
                                      right-unity-law = (\x -> (sym (deltaM-right-unity-law x))) ;
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
