open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import basic
open import delta
open import delta.functor
open import deltaM
open import nat
open import laws
open Functor

module deltaM.functor where


deltaM-preserve-id :  {l : Level} {A : Set l} {n : Nat}
                      {T : Set l -> Set l} {F : Functor T} {M : Monad T F}
                      -> (d : DeltaM M A (S n)) -> deltaM-fmap id d ≡ id d
deltaM-preserve-id {F = F}  (deltaM (mono x))  = begin
  deltaM-fmap id (deltaM (mono x))                    ≡⟨ refl ⟩
  deltaM (fmap delta-is-functor (fmap F id) (mono x)) ≡⟨ refl ⟩
  deltaM (mono (fmap F id x))                         ≡⟨ cong (\x -> deltaM (mono x)) (preserve-id F x) ⟩
  deltaM (mono (id x))                                ≡⟨ cong (\x -> deltaM (mono x)) refl ⟩
  deltaM (mono x)                                     ∎
deltaM-preserve-id {F = F} (deltaM (delta x d)) = begin
  deltaM-fmap id (deltaM (delta x d))
  ≡⟨ refl ⟩
  deltaM (fmap delta-is-functor (fmap F id) (delta x d))
  ≡⟨ refl ⟩
  deltaM (delta (fmap F id x) (fmap delta-is-functor (fmap F id) d))
  ≡⟨ cong (\x -> deltaM (delta x (fmap delta-is-functor (fmap F id) d))) (preserve-id F x) ⟩
  deltaM (delta x (fmap delta-is-functor (fmap F id) d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM (fmap delta-is-functor (fmap F id) d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-fmap id (deltaM d))
  ≡⟨ cong (\d -> appendDeltaM (deltaM (mono x)) d) (deltaM-preserve-id {F = F} (deltaM d)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM d)
  ≡⟨ refl ⟩
  deltaM (delta x d)
  ∎


deltaM-covariant : {l : Level} {A B C : Set l} {n : Nat}
                   {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                   (f : B -> C) -> (g : A -> B) -> (d : DeltaM M A (S n)) ->
                   (deltaM-fmap (f ∙ g)) d ≡ ((deltaM-fmap f) ∙ (deltaM-fmap g)) d
deltaM-covariant {F = F} f g (deltaM (mono x))    = begin
  deltaM-fmap (f ∙ g) (deltaM (mono x))              ≡⟨ refl ⟩
  deltaM (delta-fmap (fmap F (f ∙ g)) (mono x))      ≡⟨ refl ⟩
  deltaM (mono (fmap F (f ∙ g) x))                   ≡⟨ cong (\x -> (deltaM (mono x))) (covariant F g f x) ⟩
  deltaM (mono (((fmap F f) ∙ (fmap F g)) x))        ≡⟨ refl ⟩
  deltaM-fmap f (deltaM-fmap g (deltaM (mono x)))           ∎
deltaM-covariant {F = F} f g (deltaM (delta x d)) = begin
  deltaM-fmap (f ∙ g) (deltaM (delta x d))
  ≡⟨ refl ⟩
  deltaM (delta-fmap (fmap F (f ∙ g)) (delta x d))
  ≡⟨ refl ⟩
  deltaM (delta (fmap F (f ∙ g) x) (delta-fmap (fmap F (f ∙ g)) d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (fmap F (f ∙ g) x))) (deltaM (delta-fmap (fmap F (f ∙ g)) d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (fmap F (f ∙ g) x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono de)) (deltaM-fmap (f ∙ g) (deltaM d))) (covariant F g f x)  ⟩
  appendDeltaM (deltaM (mono (((fmap F f) ∙ (fmap F g)) x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (((fmap F f) ∙ (fmap F g)) x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (delta-fmap ((fmap F f) ∙ (fmap F g)) (mono x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM ((((delta-fmap (fmap F f)) ∙ (delta-fmap (fmap F g)))) (mono x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ cong (\de ->  appendDeltaM (deltaM ((((delta-fmap (fmap F f)) ∙ (delta-fmap (fmap F g)))) (mono x))) de) (deltaM-covariant {F = F} f g (deltaM d)) ⟩
  appendDeltaM (deltaM ((((delta-fmap (fmap F f)) ∙ (delta-fmap (fmap F g)))) (mono x))) (((deltaM-fmap f) ∙ (deltaM-fmap g)) (deltaM d))
  ≡⟨ refl ⟩
  (deltaM-fmap f ∙ deltaM-fmap g) (deltaM (delta x d))
  ∎



deltaM-is-functor : {l : Level} {n : Nat}
                    {T : Set l -> Set l} {F : Functor T} {M : Monad T F} ->
                    Functor {l} (\A -> DeltaM M A (S n))
deltaM-is-functor {F = F} = record { fmap         = deltaM-fmap
                                   ; preserve-id  = deltaM-preserve-id {F = F}
                                   ; covariant    = (\f g -> deltaM-covariant {F = F} g f)
                                   }


