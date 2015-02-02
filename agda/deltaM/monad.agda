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


-- sub proofs

deconstruct-id : {l : Level} {A : Set l} {n : Nat}
                 {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                 (d : DeltaM M A (S n)) -> deltaM (unDeltaM d) ≡ d
deconstruct-id {n = O}   (deltaM x) = refl
deconstruct-id {n = S n} (deltaM x) = refl



fmap-headDeltaM-with-deltaM-eta : {l : Level} {A : Set l} {n : Nat}
                                  {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                                  (x : T A) -> (fmap F ((headDeltaM {n = n} {M = M}) ∙ deltaM-eta) x) ≡ fmap F (eta M) x
fmap-headDeltaM-with-deltaM-eta {n = O}   x = refl
fmap-headDeltaM-with-deltaM-eta {n = S n} x = refl



fmap-tailDeltaM-with-deltaM-eta : {l : Level} {A : Set l} {n : Nat}
                                  {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                                  (d : DeltaM M A (S n)) ->
        deltaM-fmap ((tailDeltaM {n = n} {M = M} ) ∙ deltaM-eta) d ≡ deltaM-fmap (deltaM-eta) d
fmap-tailDeltaM-with-deltaM-eta {n = O}   d = refl
fmap-tailDeltaM-with-deltaM-eta {n = S n} d = refl



fmap-headDeltaM-with-deltaM-mu : {l : Level} {A : Set l} {n : Nat}
                                 {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                                 (x : T (DeltaM M (DeltaM M A (S n)) (S n))) ->
                   fmap F (headDeltaM ∙ deltaM-mu) x ≡ fmap F (((mu M) ∙ (fmap F headDeltaM)) ∙ headDeltaM) x
fmap-headDeltaM-with-deltaM-mu {n = O}   x = refl
fmap-headDeltaM-with-deltaM-mu {n = S n} x = refl


fmap-tailDeltaM-with-deltaM-mu : {l : Level} {A : Set l} {n : Nat}
                                 {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
               (d : DeltaM M (DeltaM M (DeltaM M A (S (S n))) (S (S n))) (S n)) ->
                deltaM-fmap (tailDeltaM ∙ deltaM-mu) d ≡ deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) d
fmap-tailDeltaM-with-deltaM-mu {n = O} (deltaM (mono x)) = refl
fmap-tailDeltaM-with-deltaM-mu {n = S n} (deltaM d)      = refl





-- main proofs

deltaM-eta-is-nt : {l : Level} {A B : Set l} {n : Nat}
                   {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                   (f : A -> B) -> (x : A) ->
                   ((deltaM-eta {l} {B} {n} {T} {F} {M} )∙ f) x ≡ deltaM-fmap f (deltaM-eta x)
deltaM-eta-is-nt {l} {A} {B} {O} {M} {fm} {mm} f x   = begin
  deltaM-eta {n = O} (f x)              ≡⟨ refl ⟩
  deltaM (mono (eta mm (f x)))          ≡⟨ cong (\de -> deltaM (mono de)) (eta-is-nt mm f x) ⟩
  deltaM (mono (fmap fm f (eta mm x)))  ≡⟨ refl ⟩
  deltaM-fmap f (deltaM-eta {n = O} x)  ∎
deltaM-eta-is-nt {l} {A} {B} {S n} {M} {fm} {mm} f x = begin
  deltaM-eta {n = S n} (f x)
  ≡⟨ refl ⟩
  deltaM (delta-eta {n = S n} (eta mm (f x)))
  ≡⟨ refl ⟩
  deltaM (delta (eta mm (f x)) (delta-eta (eta mm (f x))))
  ≡⟨ cong (\de -> deltaM (delta de (delta-eta de))) (eta-is-nt mm f x) ⟩
  deltaM (delta (fmap fm f (eta mm x)) (delta-eta (fmap fm f (eta mm x))))
  ≡⟨ cong (\de ->  deltaM (delta (fmap fm f (eta mm x)) de)) (eta-is-nt delta-is-monad (fmap fm f) (eta mm x)) ⟩
  deltaM (delta (fmap fm f (eta mm x)) (delta-fmap (fmap fm f) (delta-eta (eta mm x))))
  ≡⟨ refl ⟩
  deltaM-fmap f (deltaM-eta {n = S n} x)
  ∎




postulate deltaM-mu-is-nt : {l : Level} {A B : Set l} {n : Nat}
                  {T : Set l -> Set l} {F : Functor T} {M : Monad T F}
                  (f : A -> B) -> (d : DeltaM M (DeltaM M A (S n)) (S n)) ->
                  deltaM-fmap f (deltaM-mu d) ≡ deltaM-mu (deltaM-fmap (deltaM-fmap f) d)
{-
deltaM-mu-is-nt {l} {A} {B} {O} {T} {F} {M}  f (deltaM (mono x))      = begin
  deltaM-fmap f (deltaM-mu (deltaM (mono x)))
  ≡⟨ refl ⟩
  deltaM-fmap f (deltaM (mono (mu M (fmap F headDeltaM x))))
  ≡⟨ refl ⟩
  deltaM (mono (fmap F f (mu M (fmap F headDeltaM x))))
  ≡⟨ cong (\de -> deltaM (mono de)) (sym (mu-is-nt M f (fmap F headDeltaM x))) ⟩
  deltaM (mono (mu M (fmap F (fmap F f) (fmap F headDeltaM x))))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (sym (covariant F headDeltaM (fmap F f) x)) ⟩  
  deltaM (mono (mu M (fmap F ((fmap F f) ∙ headDeltaM) x)))
  ≡⟨ {!!} ⟩  
  deltaM (mono (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x)))
  ≡⟨ {!!} ⟩
  deltaM (mono (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x)))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (covariant F (deltaM-fmap f) (headDeltaM) x) ⟩
  deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (fmap F (deltaM-fmap f) x)))) 
  ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {M = M} (deltaM (mono (fmap F (deltaM-fmap f) x))))))) 
  ≡⟨ refl ⟩ 
  deltaM-mu (deltaM (mono (fmap F (deltaM-fmap f) x)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM-fmap (deltaM-fmap f) (deltaM (mono x)))
  ∎
deltaM-mu-is-nt {n = S n} f (deltaM (delta x d)) = {!!}

-}


deltaM-right-unity-law : {l : Level} {A : Set l} {n : Nat}
                         {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                         (d : DeltaM M A (S n)) -> (deltaM-mu ∙ deltaM-eta) d ≡ id d
deltaM-right-unity-law {l} {A} {O} {M} {fm} {mm} (deltaM (mono x)) = begin
  deltaM-mu (deltaM-eta (deltaM (mono x)))             ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (eta mm (deltaM (mono x))))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (headDeltaM {M = mm})(eta mm (deltaM (mono x))))))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (sym (eta-is-nt mm headDeltaM (deltaM (mono x)) )) ⟩
  deltaM (mono (mu mm (eta mm ((headDeltaM {l} {A} {O} {M} {fm} {mm}) (deltaM (mono x)))))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (eta mm x))) ≡⟨ cong (\de -> deltaM (mono de)) (sym (right-unity-law mm x)) ⟩
  deltaM (mono x)
  ∎
deltaM-right-unity-law {l} {A} {S n} {T} {F} {M} (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-eta (deltaM (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (eta M (deltaM (delta x d))) (delta-eta (eta M (deltaM (delta x d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {M = M} (deltaM (delta {l} {T (DeltaM M A (S (S n)))} {n} (eta M (deltaM (delta x d))) (delta-eta (eta M (deltaM (delta x d)))))))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM (deltaM (delta (eta M (deltaM (delta x d))) (delta-eta (eta M (deltaM (delta x d)))))))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (headDeltaM {M = M}) (eta M (deltaM (delta x d)))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta M (deltaM (delta x d)))))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de)
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta M (deltaM (delta x d))))))))))
     (sym (eta-is-nt M headDeltaM (deltaM (delta x d)))) ⟩
  deltaM (delta (mu M (eta M (headDeltaM {M = M} (deltaM (delta x d)))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta M (deltaM (delta x d)))))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (eta M x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta M (deltaM (delta x d)))))))))
  ≡⟨ cong (\de -> deltaM (delta de (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta M (deltaM (delta x d)))))))))) 
           (sym (right-unity-law M x)) ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta M (deltaM (delta x d)))))))))
  ≡⟨ refl ⟩ 
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM (delta-fmap (fmap F tailDeltaM) (delta-eta (eta M (deltaM (delta x d)))))))))
  ≡⟨ cong (\de -> deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM de)))))
           (sym (delta-eta-is-nt (fmap F tailDeltaM)  (eta M (deltaM (delta x d))))) ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM (delta-eta (fmap F tailDeltaM (eta M (deltaM (delta x d)))))))))
  ≡⟨ cong (\de -> deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM (delta-eta de))))))
           (sym (eta-is-nt M tailDeltaM (deltaM (delta x d)))) ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM (delta-eta (eta M (tailDeltaM (deltaM (delta x d)))))))))
  ≡⟨ refl ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM (delta-eta (eta M (deltaM d)))))))
  ≡⟨ refl ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM-eta (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta x (unDeltaM {M = M} de))) (deltaM-right-unity-law (deltaM d)) ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM d)))
  ≡⟨ refl ⟩
  deltaM (delta x d)
  ∎



{-


postulate deltaM-left-unity-law : {l : Level} {A : Set l}
                        {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM}
                        {n : Nat}
                        (d : DeltaM M {functorM} {monadM} A (S n)) ->
                              (deltaM-mu ∙ (deltaM-fmap deltaM-eta)) d ≡ id d
{-
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

-}
postulate nya : {l : Level} {A : Set l}
                         (M : Set l -> Set l) (fm : Functor M) (mm : Monad M fm)
                         (d : DeltaM M {fm} {mm} (DeltaM M {fm} {mm} (DeltaM M {fm} {mm} A (S O)) (S O))  (S O)) ->
                         deltaM-mu (deltaM-fmap deltaM-mu d) ≡ deltaM-mu (deltaM-mu d)







deltaM-association-law : {l : Level} {A : Set l} {n : Nat}
                         (M : Set l -> Set l) (fm : Functor M) (mm : Monad M fm)
                         (d : DeltaM M {fm} {mm} (DeltaM M {fm} {mm} (DeltaM M {fm} {mm} A (S n)) (S n))  (S n)) ->
                         deltaM-mu (deltaM-fmap deltaM-mu d) ≡ deltaM-mu (deltaM-mu d)
deltaM-association-law {l} {A} {O} M fm mm (deltaM (mono x))    = nya {l} {A} M fm mm (deltaM (mono x))
{-
begin
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (mono x))) ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (fmap fm deltaM-mu x))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (headDeltaM {A = DeltaM M A (S O)} {monadM = mm} (deltaM (mono (fmap fm deltaM-mu x))))))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x)))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (headDeltaM {A = A} {monadM = mm}) (fmap fm
    (\d -> (deltaM (mono (mu mm (fmap fm headDeltaM ((headDeltaM {l} {DeltaM M A (S O)} {monadM = mm}) d)))))) x))))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de)))
           (sym (covariant fm (\d -> (deltaM (mono (mu mm (fmap fm headDeltaM ((headDeltaM {l} {DeltaM M A (S O)} {monadM = mm}) d))))))  headDeltaM x)) ⟩
  deltaM (mono (mu mm (fmap fm ((headDeltaM {A = A} {monadM = mm}) ∙
    (\d -> (deltaM (mono (mu mm (fmap fm headDeltaM ((headDeltaM {l} {DeltaM M A (S O)} {monadM = mm}) d))))))) x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (\d -> (headDeltaM {A = A} {monadM = mm} (deltaM (mono (mu mm (fmap fm headDeltaM ((headDeltaM {l} {DeltaM M A (S O)} {monadM = mm}) d))))))) x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (\d -> (mu mm (fmap fm headDeltaM ((headDeltaM {l} {DeltaM M A (S O)} {monadM = mm}) d)))) x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm ((mu mm) ∙  (((fmap fm headDeltaM)) ∙  ((headDeltaM {l} {DeltaM M A (S O)} {monadM = mm})))) x)))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (covariant fm ((fmap fm headDeltaM) ∙ (headDeltaM)) (mu mm) x )⟩
  deltaM (mono (mu mm (((fmap fm (mu mm)) ∙ (fmap fm ((fmap fm headDeltaM) ∙  (headDeltaM {l} {DeltaM M A (S O)} {monadM = mm})))) x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (mu mm) ((fmap fm ((fmap fm headDeltaM) ∙ (headDeltaM {l} {DeltaM M A (S O)} {monadM = mm}))) x))))
  ≡⟨ cong (\de -> deltaM (mono (mu mm (fmap fm (mu mm) de)))) (covariant fm headDeltaM (fmap fm headDeltaM) x) ⟩
  deltaM (mono (mu mm (fmap fm (mu mm) (((fmap fm (fmap fm headDeltaM)) ∙ (fmap fm (headDeltaM {l} {DeltaM M A (S O)} {monadM = mm}))) x))))
  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (mu mm) (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x)))))
  ≡⟨ cong (\de ->   deltaM (mono de)) (association-law mm (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x))) ⟩
  deltaM (mono (mu mm (mu mm (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x)))))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (mu-is-nt mm headDeltaM (fmap fm headDeltaM x)) ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x)))))  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (headDeltaM {A = DeltaM M A (S O)} {monadM = mm} (deltaM (mono (mu mm (fmap fm headDeltaM x))))))))  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (mu mm (fmap fm headDeltaM x))))  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (mu mm (fmap fm headDeltaM (headDeltaM  {A = DeltaM M (DeltaM M A (S O)) (S O)} {monadM = mm} (deltaM (mono x)))))))  ≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (mono x)))  ∎
-}
deltaM-association-law {l} {A} {S n} M fm mm (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (fmap fm deltaM-mu x) (delta-fmap (fmap fm deltaM-mu) d)))
  ≡⟨ refl ⟩
  deltaM (delta (mu mm (fmap fm (headDeltaM {A = A} {monadM = mm}) (headDeltaM {A = DeltaM M A (S (S n))} {monadM = mm} (deltaM (delta (fmap fm deltaM-mu x) (delta-fmap (fmap fm deltaM-mu) d))))))
                (unDeltaM {A = A} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM (deltaM (delta (fmap fm deltaM-mu x) (delta-fmap (fmap fm deltaM-mu) d))))))))

  ≡⟨ refl ⟩
  deltaM (delta (mu mm (fmap fm (headDeltaM {A = A} {monadM = mm}) (fmap fm deltaM-mu x)))
                (unDeltaM {A = A} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-mu) d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm de) (unDeltaM {A = A} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-mu) d)))))))
           (sym (covariant fm deltaM-mu headDeltaM x)) ⟩
  deltaM (delta (mu mm (fmap fm ((headDeltaM {A = A} {monadM = mm}) ∙  deltaM-mu) x))
                (unDeltaM {A = A} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-mu) d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm de)
                          (unDeltaM {A = A} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-mu) d)))))))
           (fmap-headDeltaM-with-deltaM-mu {A = A} {monadM = mm} x) ⟩
  deltaM (delta (mu mm (fmap fm (((mu mm) ∙ (fmap fm headDeltaM)) ∙ headDeltaM) x))
                (unDeltaM {A = A} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-mu) d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu mm (fmap fm (((mu mm) ∙ (fmap fm headDeltaM)) ∙ headDeltaM) x))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM-fmap deltaM-mu (deltaM d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm (fmap fm (((mu mm) ∙ (fmap fm headDeltaM)) ∙ headDeltaM) x))
                                 (unDeltaM {monadM = mm} (deltaM-mu de))))
           (sym (deltaM-covariant fm tailDeltaM deltaM-mu (deltaM d))) ⟩
  deltaM (delta (mu mm (fmap fm (((mu mm) ∙ (fmap fm headDeltaM)) ∙ headDeltaM) x))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap (tailDeltaM ∙ deltaM-mu) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm (fmap fm (((mu mm) ∙ (fmap fm headDeltaM)) ∙ headDeltaM) x))
                                 (unDeltaM {monadM = mm} (deltaM-mu de))))
           (fmap-tailDeltaM-with-deltaM-mu (deltaM d))  ⟩
  deltaM (delta (mu mm (fmap fm (((mu mm) ∙ (fmap fm headDeltaM)) ∙ headDeltaM) x))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm de)
                          (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d))))))
          (covariant fm headDeltaM ((mu mm) ∙ (fmap fm headDeltaM)) x) ⟩
  deltaM (delta (mu mm (((fmap fm ((mu mm) ∙ (fmap fm headDeltaM))) ∙ (fmap fm headDeltaM)) x))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ refl ⟩
  deltaM (delta (mu mm (((fmap fm ((mu mm) ∙ (fmap fm headDeltaM))) (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm de)
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d))))))
           (covariant fm (fmap fm headDeltaM)  (mu mm) (fmap fm headDeltaM x)) ⟩

  deltaM (delta (mu mm ((((fmap fm (mu mm)) ∙ (fmap fm (fmap fm headDeltaM))) (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ refl ⟩
  deltaM (delta (mu mm (fmap fm (mu mm) (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta de (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d))))))
           (association-law mm (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x))) ⟩
  deltaM (delta (mu mm (mu mm (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm de) (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d))))))
           (mu-is-nt mm headDeltaM (fmap fm headDeltaM x)) ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de ->   deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x)))) (unDeltaM {monadM = mm} (deltaM-mu de))))
           (deltaM-covariant fm (deltaM-mu ∙ (deltaM-fmap tailDeltaM)) tailDeltaM (deltaM d)) ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (((deltaM-fmap (deltaM-mu ∙ (deltaM-fmap tailDeltaM))  ∙ (deltaM-fmap tailDeltaM)) (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (((deltaM-fmap (deltaM-mu ∙ (deltaM-fmap tailDeltaM)) (deltaM-fmap tailDeltaM (deltaM d))))))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x)))) (unDeltaM {monadM = mm} (deltaM-mu de))))
           (deltaM-covariant fm deltaM-mu (deltaM-fmap tailDeltaM) (deltaM-fmap tailDeltaM (deltaM d)))  ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (((deltaM-fmap deltaM-mu) ∙ (deltaM-fmap (deltaM-fmap tailDeltaM))) (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap deltaM-mu (deltaM-fmap (deltaM-fmap tailDeltaM) (deltaM-fmap tailDeltaM (deltaM d)))))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x)))) (unDeltaM {monadM = mm} de)))
           (deltaM-association-law M fm mm (deltaM-fmap (deltaM-fmap tailDeltaM) (deltaM-fmap tailDeltaM (deltaM d)))) ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-mu (deltaM-fmap (deltaM-fmap tailDeltaM) (deltaM-fmap tailDeltaM (deltaM d)))))))

  ≡⟨ cong (\de -> deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                                 (unDeltaM {monadM = mm} (deltaM-mu de))))
           (sym (deltaM-mu-is-nt tailDeltaM (deltaM-fmap tailDeltaM (deltaM d)))) ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d)))))))
  ≡⟨ cong (\de -> deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                                 (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM de)))))
           (sym (deconstruct-id (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))) ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM
                  (deltaM (unDeltaM {A = DeltaM M A (S (S n))} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d)))))))))


  ≡⟨ refl ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (headDeltaM {monadM = mm} ((deltaM (delta (mu mm (fmap fm headDeltaM x))
                           (unDeltaM {A = DeltaM M A (S (S n))} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))))))
                (unDeltaM {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM ((deltaM (delta (mu mm (fmap fm headDeltaM x))
                           (unDeltaM {A = DeltaM M A (S (S n))} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))))))))


  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (mu mm (fmap fm headDeltaM x))
                           (unDeltaM {A = DeltaM M A (S (S n))} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (mu mm (fmap fm headDeltaM (headDeltaM {monadM = mm} (deltaM (delta x d)))))
                           (unDeltaM {A = DeltaM M A (S (S n))} {monadM = mm} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM (deltaM (delta x d))))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (delta x d)))
  ∎
{-
deltaM-association-law {l} {A} {S n} M fm mm (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (delta x d))) ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta-fmap (fmap fm deltaM-mu) (delta x d))) ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (fmap fm deltaM-mu x) (delta-fmap (fmap fm deltaM-mu) d))) ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x)))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-mu) d)))) ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x)))))
               (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) (delta-fmap (fmap fm deltaM-mu) d))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x))))) de)
           (sym (deconstruct-id (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) (delta-fmap (fmap fm deltaM-mu) d)))))) ⟩

  appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x)))))
               (deltaM (deconstruct {A = A} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) (delta-fmap (fmap fm deltaM-mu) d))))))
  ≡⟨ refl ⟩
  deltaM (deltaAppend (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x))))
                      (deconstruct {A = A} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) (delta-fmap (fmap fm deltaM-mu) d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x)))
                (deconstruct {A = A} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) (delta-fmap (fmap fm deltaM-mu) d))))))
  ≡⟨ {!!} ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d)))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))))
               (deltaM-mu (deltaM-fmap tailDeltaM de)))
           (sym (deconstruct-id (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d))))) ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (deconstruct {A = DeltaM M A (S (S n))} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d)))))))

  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM ( (deltaM (delta (mu mm (fmap fm headDeltaM x))
                          (deconstruct {A = DeltaM M A (S (S n))} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d))))))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm (headDeltaM {monadM = mm}) (headDeltaM {monadM = mm} ((deltaM (delta (mu mm (fmap fm headDeltaM x))
                           (deconstruct {A = DeltaM M A (S (S n))} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d))))))))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM ( (deltaM (delta (mu mm (fmap fm headDeltaM x))
                           (deconstruct {A = DeltaM M A (S (S n))} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d))))))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (mu mm (fmap fm headDeltaM x))
                           (deconstruct {A = DeltaM M A (S (S n))} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (deltaAppend (mono (mu mm (fmap fm headDeltaM x)))
                                 (deconstruct {A = DeltaM M A (S (S n))} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d))))))
  ≡⟨ refl ⟩
  deltaM-mu (appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM x))))
                          (deltaM (deconstruct {A = DeltaM M A (S (S n))} {mm = mm} (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d))))))
  ≡⟨ cong (\de -> deltaM-mu (appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM x)))) de))
           (deconstruct-id (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d)))) ⟩
  deltaM-mu (appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM x))))
                          (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) d))))
  ≡⟨ refl ⟩
  deltaM-mu (appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM x))))
                          (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (delta x d)))
  ∎
-}



deltaM-is-monad : {l : Level} {A : Set l} {n : Nat}
                              {M : Set l -> Set l}
                              (functorM : Functor M)
                              (monadM   : Monad M functorM) ->
               Monad {l} (\A -> DeltaM M {functorM} {monadM} A (S n)) (deltaM-is-functor {l} {n})
deltaM-is-monad {l} {A} {n} {M} functorM monadM =
                record { mu     = deltaM-mu
                       ; eta    = deltaM-eta
                       ; eta-is-nt = deltaM-eta-is-nt
                       ; mu-is-nt = (\f x -> (sym (deltaM-mu-is-nt f x)))
                       ; association-law = (deltaM-association-law M functorM monadM)
                       ; left-unity-law  = deltaM-left-unity-law
                       ; right-unity-law = (\x -> (sym (deltaM-right-unity-law x)))
                       }


-}
