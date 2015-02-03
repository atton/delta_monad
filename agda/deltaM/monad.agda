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

headDeltaM-with-f : {l : Level} {A B : Set l} {n : Nat}
                    {T : Set l -> Set l} {F : Functor T} {M : Monad T F}
                    (f : A -> B) -> (x : (DeltaM M A (S n))) ->
                    ((fmap F f) ∙ headDeltaM) x ≡ (headDeltaM ∙ (deltaM-fmap f)) x
headDeltaM-with-f {n = O} f   (deltaM (mono x))    = refl
headDeltaM-with-f {n = S n} f (deltaM (delta x d)) = refl

tailDeltaM-with-f : {l : Level} {A B : Set l} {n : Nat}
                    {T : Set l -> Set l} {F : Functor T} {M : Monad T F}
                    (f : A -> B) -> (d : (DeltaM M A (S (S n)))) ->
                    (tailDeltaM ∙ (deltaM-fmap f)) d ≡ ((deltaM-fmap f) ∙ tailDeltaM) d
tailDeltaM-with-f {n = O} f (deltaM (delta x d))   = refl
tailDeltaM-with-f {n = S n} f (deltaM (delta x d)) = refl

headDeltaM-with-deltaM-eta : {l : Level} {A : Set l} {n : Nat}
                             {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                             (x : DeltaM M A (S n)) ->
                             ((headDeltaM {n = n} {M = M}) ∙ deltaM-eta) x ≡ eta M x
headDeltaM-with-deltaM-eta {n = O} (deltaM (mono x))      = refl
headDeltaM-with-deltaM-eta {n = S n} (deltaM (delta x d)) = refl


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




deltaM-mu-is-nt : {l : Level} {A B : Set l} {n : Nat}
                  {T : Set l -> Set l} {F : Functor T} {M : Monad T F}
                  (f : A -> B) -> (d : DeltaM M (DeltaM M A (S n)) (S n)) ->
                  deltaM-fmap f (deltaM-mu d) ≡ deltaM-mu (deltaM-fmap (deltaM-fmap f) d)
deltaM-mu-is-nt {l} {A} {B} {O} {T} {F} {M}  f (deltaM (mono x)) = begin
  deltaM-fmap f (deltaM-mu (deltaM (mono x)))
  ≡⟨ refl ⟩
  deltaM-fmap f (deltaM (mono (mu M (fmap F headDeltaM x))))
  ≡⟨ refl ⟩
  deltaM (mono (fmap F f (mu M (fmap F headDeltaM x))))
  ≡⟨ cong (\de -> deltaM (mono de)) (sym (mu-is-nt M f (fmap F headDeltaM x))) ⟩
  deltaM (mono (mu M (fmap F (fmap F f) (fmap F headDeltaM x))))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (sym (covariant F headDeltaM (fmap F f) x)) ⟩
  deltaM (mono (mu M (fmap F ((fmap F f) ∙ headDeltaM) x)))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (fmap-equiv F (headDeltaM-with-f f) x) ⟩
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
deltaM-mu-is-nt {l} {A} {B} {S n} {T} {F} {M} f (deltaM (delta x d)) = begin
  deltaM-fmap f (deltaM-mu (deltaM (delta x d))) ≡⟨ refl ⟩
  deltaM-fmap f (deltaM (delta (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {M = M} (deltaM (delta x d)))))
                               (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM (deltaM (delta x d))))))))
  ≡⟨ refl ⟩
  deltaM-fmap f (deltaM (delta (mu M (fmap F (headDeltaM {M = M}) x))
                               (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM (delta (fmap F f (mu M (fmap F (headDeltaM {M = M}) x)))
                (delta-fmap (fmap F f) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ cong (\de -> deltaM (delta de
                  (delta-fmap (fmap F f) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d)))))))
           (sym (mu-is-nt M f (fmap F headDeltaM x)))  ⟩
  deltaM (delta (mu M (fmap F (fmap F f) (fmap F (headDeltaM {M = M}) x)))
                (delta-fmap (fmap F f) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de) (delta-fmap (fmap F f) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d)))))))
           (sym (covariant F headDeltaM (fmap F f) x)) ⟩
  deltaM (delta (mu M (fmap F ((fmap F f) ∙ (headDeltaM {M = M})) x))
                (delta-fmap (fmap F f) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de) (delta-fmap (fmap F f) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d)))))))
           (fmap-equiv F (headDeltaM-with-f f) x)  ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x))
                (delta-fmap (fmap F f) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x))
                (unDeltaM {M = M} (deltaM-fmap f (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x)) (unDeltaM de)))
           (deltaM-mu-is-nt {l} {A} {B} {n} {T} {F} {M} f (deltaM-fmap tailDeltaM (deltaM d))) ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap (deltaM-fmap {n = n} f) (deltaM-fmap {n = n} (tailDeltaM {n = n}) (deltaM d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x)) (unDeltaM {M = M} (deltaM-mu de))))
           (sym (deltaM-covariant (deltaM-fmap f) tailDeltaM (deltaM d))) ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap {n = n} ((deltaM-fmap {n = n} f) ∙ (tailDeltaM {n = n})) (deltaM d)))))

  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x)) (unDeltaM {M = M} (deltaM-mu de))))
               (sym (deltaM-fmap-equiv (tailDeltaM-with-f f) (deltaM d))) ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap (tailDeltaM ∙ (deltaM-fmap f)) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x)) (unDeltaM {M = M} (deltaM-mu de))))
           (deltaM-covariant tailDeltaM (deltaM-fmap f) (deltaM d)) ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM-fmap (deltaM-fmap f) (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {M = M}) ∙ (deltaM-fmap f)) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F (deltaM-fmap f)) d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F (deltaM-fmap f)) d)))))))
           (covariant F (deltaM-fmap f) headDeltaM x) ⟩
  deltaM (delta (mu M (fmap F (headDeltaM {M = M}) (fmap F (deltaM-fmap f) x)))
                      (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F (deltaM-fmap f)) d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {M = M} (deltaM (delta (fmap F (deltaM-fmap f) x) (delta-fmap (fmap F (deltaM-fmap f)) d))))))
                      (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM (deltaM (delta (fmap F (deltaM-fmap f) x) (delta-fmap (fmap F (deltaM-fmap f)) d))))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (fmap F (deltaM-fmap f) x) (delta-fmap (fmap F (deltaM-fmap f)) d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM-fmap (deltaM-fmap f) (deltaM (delta x d)))
  ∎





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






deltaM-left-unity-law : {l : Level} {A : Set l} {n : Nat}
                        {T : Set l -> Set l} {F : Functor T} {M : Monad T F}
                        (d : DeltaM M A (S n)) -> (deltaM-mu ∙ (deltaM-fmap deltaM-eta)) d ≡ id d
deltaM-left-unity-law {l} {A}   {O} {T} {F} {M} (deltaM (mono x)) = begin
  deltaM-mu (deltaM-fmap deltaM-eta (deltaM (mono x))) ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (fmap F deltaM-eta x)))      ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {M = M} (deltaM (mono (fmap F deltaM-eta x)))))))      ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (fmap F deltaM-eta x))))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (sym (covariant F deltaM-eta headDeltaM x)) ⟩
  deltaM (mono (mu M (fmap F ((headDeltaM {n = O} {M = M}) ∙ deltaM-eta) x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (eta M) x)))
  ≡⟨ cong (\de -> deltaM (mono de)) (left-unity-law M x) ⟩
  deltaM (mono x)
  ∎
deltaM-left-unity-law {l} {A} {S n} {T} {F} {M} (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-fmap deltaM-eta (deltaM (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (fmap F deltaM-eta x) (delta-fmap (fmap F deltaM-eta) d)))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (headDeltaM {n = S n} {M = M}) (headDeltaM {n = S n} {M = M} (deltaM (delta (fmap F deltaM-eta x) (delta-fmap (fmap F deltaM-eta) d))))))
  (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM (deltaM (delta (fmap F deltaM-eta x) (delta-fmap (fmap F deltaM-eta) d))))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (headDeltaM {n = S n} {M = M}) (fmap F deltaM-eta x)))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-eta) d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-eta) d)))))))
           (sym (covariant F deltaM-eta headDeltaM x)) ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {n = S n} {M = M}) ∙  deltaM-eta) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-eta) d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (eta M) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-eta) d))))))
  ≡⟨ cong (\de -> deltaM (delta de (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-eta) d)))))))
           (left-unity-law M x) ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-eta) d))))))
  ≡⟨ refl ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM-fmap (tailDeltaM {n = n})(deltaM-fmap (deltaM-eta {n = S n})(deltaM d))))))
  ≡⟨ cong (\de -> deltaM (delta x (unDeltaM {M = M} (deltaM-mu de)))) (sym (deltaM-covariant tailDeltaM deltaM-eta (deltaM d))) ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((tailDeltaM {n = n}) ∙ (deltaM-eta {n = S n})) (deltaM d)))))
  ≡⟨ refl ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM-mu (deltaM-fmap deltaM-eta (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta x (unDeltaM {M = M} de))) (deltaM-left-unity-law (deltaM d)) ⟩
  deltaM (delta x (unDeltaM {M = M} (deltaM d)))
  ≡⟨ refl ⟩
  deltaM (delta x d)
  ∎

deltaM-association-law : {l : Level} {A : Set l} {n : Nat}
                         {T : Set l -> Set l} {F : Functor T} {M : Monad T F}
                         (d : DeltaM M (DeltaM M (DeltaM M A (S n)) (S n))  (S n)) ->
                         deltaM-mu (deltaM-fmap deltaM-mu d) ≡ deltaM-mu (deltaM-mu d)
deltaM-association-law {l} {A}   {O} {T} {F} {M} (deltaM (mono x))    = begin
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (mono x)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (fmap F deltaM-mu x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {M = M} (deltaM (mono (fmap F deltaM-mu x)))))))
  ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (fmap F deltaM-mu x))))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (sym (covariant F deltaM-mu headDeltaM x)) ⟩
  deltaM (mono (mu M (fmap F ((headDeltaM {M = M}) ∙ deltaM-mu) x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (((mu M) ∙ (fmap F headDeltaM)) ∙ headDeltaM) x)))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (covariant F headDeltaM ((mu M) ∙ (fmap F headDeltaM)) x) ⟩
  deltaM (mono (mu M ((((fmap F (((mu M) ∙ (fmap F headDeltaM)))) ∙ (fmap F headDeltaM)) x))))
  ≡⟨ refl ⟩
  deltaM (mono (mu M ((((fmap F (((mu M) ∙ (fmap F headDeltaM)))) (fmap F headDeltaM x))))))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (covariant F (fmap F headDeltaM) (mu M) (fmap F headDeltaM x)) ⟩
  deltaM (mono (mu M (((fmap F (mu M)) ∙ (fmap F (fmap F headDeltaM))) (fmap F headDeltaM x))))
  ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (mu M) ((fmap F (fmap F headDeltaM) (fmap F headDeltaM x))))))
  ≡⟨ cong (\de -> deltaM (mono de)) (association-law M (fmap F (fmap F headDeltaM) (fmap F headDeltaM x))) ⟩
  deltaM (mono (mu M (mu M (fmap F (fmap F headDeltaM) (fmap F headDeltaM x)))))
  ≡⟨ cong (\de -> deltaM (mono (mu M de))) (mu-is-nt M headDeltaM (fmap F headDeltaM x)) ⟩
  deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (mu M (fmap F (headDeltaM {M = M}) x)))))
  ≡⟨ refl ⟩
  deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {M = M} (deltaM (mono (mu M (fmap F (headDeltaM {M = M}) x))))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (mu M (fmap F (headDeltaM {M = M}) x))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {M = M} (deltaM (mono x)))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (mono x)))

  ∎

deltaM-association-law {l} {A} {S n} {T} {F} {M} (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (fmap F deltaM-mu x) (delta-fmap (fmap F deltaM-mu) d)))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (headDeltaM {M = M}) (headDeltaM {A = DeltaM M A (S (S n))} {M = M} (deltaM (delta (fmap F deltaM-mu x) (delta-fmap (fmap F deltaM-mu) d))))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM (deltaM (delta (fmap F deltaM-mu x) (delta-fmap (fmap F deltaM-mu) d))))))))

  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (headDeltaM {A = A} {M = M}) (fmap F deltaM-mu x)))
                (unDeltaM {A = A} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-mu) d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de) (unDeltaM {A = A} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-mu) d)))))))
           (sym (covariant F deltaM-mu headDeltaM x)) ⟩
  deltaM (delta (mu M (fmap F ((headDeltaM {A = A} {M = M}) ∙  deltaM-mu) x))
                (unDeltaM {A = A} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-mu) d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de)
                          (unDeltaM {A = A} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-mu) d)))))))
           (fmap-headDeltaM-with-deltaM-mu {A = A} {M = M} x) ⟩
  deltaM (delta (mu M (fmap F (((mu M) ∙ (fmap F headDeltaM)) ∙ headDeltaM) x))
                (unDeltaM {A = A} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap F deltaM-mu) d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (((mu M) ∙ (fmap F headDeltaM)) ∙ headDeltaM) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM-fmap deltaM-mu (deltaM d))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F (((mu M) ∙ (fmap F headDeltaM)) ∙ headDeltaM) x))
                                 (unDeltaM {M = M} (deltaM-mu de))))
           (sym (deltaM-covariant tailDeltaM deltaM-mu (deltaM d))) ⟩
  deltaM (delta (mu M (fmap F (((mu M) ∙ (fmap F headDeltaM)) ∙ headDeltaM) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap (tailDeltaM ∙ deltaM-mu) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F (((mu M) ∙ (fmap F headDeltaM)) ∙ headDeltaM) x))
                                 (unDeltaM {M = M} (deltaM-mu de))))
           (fmap-tailDeltaM-with-deltaM-mu (deltaM d))  ⟩
  deltaM (delta (mu M (fmap F (((mu M) ∙ (fmap F headDeltaM)) ∙ headDeltaM) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de)
                          (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d))))))
          (covariant F headDeltaM ((mu M) ∙ (fmap F headDeltaM)) x) ⟩
  deltaM (delta (mu M (((fmap F ((mu M) ∙ (fmap F headDeltaM))) ∙ (fmap F headDeltaM)) x))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (((fmap F ((mu M) ∙ (fmap F headDeltaM))) (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de)
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d))))))
           (covariant F (fmap F headDeltaM)  (mu M) (fmap F headDeltaM x)) ⟩

  deltaM (delta (mu M ((((fmap F (mu M)) ∙ (fmap F (fmap F headDeltaM))) (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F (mu M) (fmap F (fmap F headDeltaM) (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta de (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d))))))
           (association-law M (fmap F (fmap F headDeltaM) (fmap F headDeltaM x))) ⟩
  deltaM (delta (mu M (mu M (fmap F (fmap F headDeltaM) (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de -> deltaM (delta (mu M de) (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d))))))
           (mu-is-nt M headDeltaM (fmap F headDeltaM x)) ⟩
  deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap ((deltaM-mu ∙ (deltaM-fmap tailDeltaM)) ∙ tailDeltaM) (deltaM d)))))
  ≡⟨ cong (\de ->   deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x)))) (unDeltaM {M = M} (deltaM-mu de))))
           (deltaM-covariant (deltaM-mu ∙ (deltaM-fmap tailDeltaM)) tailDeltaM (deltaM d)) ⟩
  deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (((deltaM-fmap (deltaM-mu ∙ (deltaM-fmap tailDeltaM))  ∙ (deltaM-fmap tailDeltaM)) (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (((deltaM-fmap (deltaM-mu ∙ (deltaM-fmap tailDeltaM)) (deltaM-fmap tailDeltaM (deltaM d))))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x)))) (unDeltaM {M = M} (deltaM-mu de))))
           (deltaM-covariant deltaM-mu (deltaM-fmap tailDeltaM) (deltaM-fmap tailDeltaM (deltaM d)))  ⟩
  deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (((deltaM-fmap deltaM-mu) ∙ (deltaM-fmap (deltaM-fmap tailDeltaM))) (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap deltaM-mu (deltaM-fmap (deltaM-fmap tailDeltaM) (deltaM-fmap tailDeltaM (deltaM d)))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x)))) (unDeltaM {M = M} de)))
           (deltaM-association-law (deltaM-fmap (deltaM-fmap tailDeltaM) (deltaM-fmap tailDeltaM (deltaM d)))) ⟩
  deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-mu (deltaM-fmap (deltaM-fmap tailDeltaM) (deltaM-fmap tailDeltaM (deltaM d)))))))

  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                                 (unDeltaM {M = M} (deltaM-mu de))))
           (sym (deltaM-mu-is-nt tailDeltaM (deltaM-fmap tailDeltaM (deltaM d)))) ⟩
  deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d)))))))
  ≡⟨ cong (\de -> deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                                 (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM de)))))
           (sym (deconstruct-id (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))) ⟩
  deltaM (delta (mu M (fmap F headDeltaM (mu M (fmap F headDeltaM x))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM
                  (deltaM (unDeltaM {A = DeltaM M A (S (S n))} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d)))))))))


  ≡⟨ refl ⟩
  deltaM (delta (mu M (fmap F headDeltaM (headDeltaM {M = M} ((deltaM (delta (mu M (fmap F headDeltaM x))
                           (unDeltaM {A = DeltaM M A (S (S n))} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))))))
                (unDeltaM {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM ((deltaM (delta (mu M (fmap F headDeltaM x))
                           (unDeltaM {A = DeltaM M A (S (S n))} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))))))))


  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (mu M (fmap F headDeltaM x))
                           (unDeltaM {A = DeltaM M A (S (S n))} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (mu M (fmap F headDeltaM (headDeltaM {M = M} (deltaM (delta x d)))))
                           (unDeltaM {A = DeltaM M A (S (S n))} {M = M} (deltaM-mu (deltaM-fmap tailDeltaM (tailDeltaM (deltaM (delta x d))))))))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (delta x d)))
  ∎




deltaM-is-monad : {l : Level} {A : Set l} {n : Nat}
                  {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                  Monad {l} (\A -> DeltaM M A (S n)) (deltaM-is-functor {l} {n})
deltaM-is-monad {l} {A} {n} {T} {F} {M} =
                record { mu     = deltaM-mu
                       ; eta    = deltaM-eta
                       ; eta-is-nt = deltaM-eta-is-nt
                       ; mu-is-nt = (\f x -> (sym (deltaM-mu-is-nt f x)))
                       ; association-law = deltaM-association-law
                       ; left-unity-law  = deltaM-left-unity-law
                       ; right-unity-law = (\x -> (sym (deltaM-right-unity-law x)))
                       }




