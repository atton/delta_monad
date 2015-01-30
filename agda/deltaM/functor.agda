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
                      {M : Set l -> Set l}
                      (functorM : Functor  M)
                      {monadM   : Monad  M functorM}
                      -> (d : DeltaM M {functorM} {monadM} A (S n)) -> deltaM-fmap id d ≡ id d
deltaM-preserve-id functorM (deltaM (mono x))  = begin
  deltaM-fmap id (deltaM (mono x))                           ≡⟨ refl ⟩
  deltaM (fmap delta-is-functor (fmap functorM id) (mono x)) ≡⟨ refl ⟩
  deltaM (mono (fmap functorM id x))                         ≡⟨ cong (\x -> deltaM (mono x)) (preserve-id functorM x) ⟩
  deltaM (mono (id x))                                       ≡⟨ cong (\x -> deltaM (mono x)) refl ⟩
  deltaM (mono x)                                            ∎
deltaM-preserve-id functorM (deltaM (delta x d)) = begin
  deltaM-fmap id (deltaM (delta x d))
  ≡⟨ refl ⟩
  deltaM (fmap delta-is-functor (fmap functorM id) (delta x d))
  ≡⟨ refl ⟩
  deltaM (delta (fmap functorM id x) (fmap delta-is-functor (fmap functorM id) d))
  ≡⟨ cong (\x -> deltaM (delta x (fmap delta-is-functor (fmap functorM id) d))) (preserve-id functorM x) ⟩
  deltaM (delta x (fmap delta-is-functor (fmap functorM id) d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM (fmap delta-is-functor (fmap functorM id) d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-fmap id (deltaM d))
  ≡⟨ cong (\d -> appendDeltaM (deltaM (mono x)) d) (deltaM-preserve-id functorM (deltaM d)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM d)
  ≡⟨ refl ⟩
  deltaM (delta x d)
  ∎


deltaM-covariant : {l : Level} {A B C : Set l} {n : Nat} ->
                   {M : Set l -> Set l}
                   (functorM : Functor M)
                   {monadM   : Monad M functorM}
                   (f : B -> C) -> (g : A -> B) -> (d : DeltaM M {functorM} {monadM} A (S n)) ->
                   (deltaM-fmap (f ∙ g)) d ≡ ((deltaM-fmap f) ∙ (deltaM-fmap g)) d
deltaM-covariant functorM f g (deltaM (mono x))    = begin
  deltaM-fmap (f ∙ g) (deltaM (mono x))                     ≡⟨ refl ⟩
  deltaM (delta-fmap (fmap functorM (f ∙ g)) (mono x))      ≡⟨ refl ⟩
  deltaM (mono (fmap functorM (f ∙ g) x))                   ≡⟨ cong (\x -> (deltaM (mono x))) (covariant functorM g f x) ⟩
  deltaM (mono (((fmap functorM f) ∙ (fmap functorM g)) x)) ≡⟨ refl ⟩
  deltaM-fmap f (deltaM-fmap g (deltaM (mono x)))           ∎
deltaM-covariant functorM f g (deltaM (delta x d)) = begin
  deltaM-fmap (f ∙ g) (deltaM (delta x d))
  ≡⟨ refl ⟩
  deltaM (delta-fmap (fmap functorM (f ∙ g)) (delta x d))
  ≡⟨ refl ⟩
  deltaM (delta (fmap functorM (f ∙ g) x) (delta-fmap (fmap functorM (f ∙ g)) d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (fmap functorM (f ∙ g) x))) (deltaM (delta-fmap (fmap functorM (f ∙ g)) d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (fmap functorM (f ∙ g) x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono de)) (deltaM-fmap (f ∙ g) (deltaM d))) (covariant functorM g f x)  ⟩
  appendDeltaM (deltaM (mono (((fmap functorM f) ∙ (fmap functorM g)) x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (((fmap functorM f) ∙ (fmap functorM g)) x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (delta-fmap ((fmap functorM f) ∙ (fmap functorM g)) (mono x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM ((((delta-fmap (fmap functorM f)) ∙ (delta-fmap (fmap functorM g)))) (mono x))) (deltaM-fmap (f ∙ g) (deltaM d))
  ≡⟨ cong (\de ->  appendDeltaM (deltaM ((((delta-fmap (fmap functorM f)) ∙ (delta-fmap (fmap functorM g)))) (mono x))) de) (deltaM-covariant functorM f g (deltaM d)) ⟩
  appendDeltaM (deltaM ((((delta-fmap (fmap functorM f)) ∙ (delta-fmap (fmap functorM g)))) (mono x))) (((deltaM-fmap f) ∙ (deltaM-fmap g)) (deltaM d))
  ≡⟨ refl ⟩
  (deltaM-fmap f ∙ deltaM-fmap g) (deltaM (delta x d))
  ∎

postulate deltaM-fmap-equiv : {l : Level} {A B : Set l} {n : Nat}
                                {M : Set l -> Set l}
                                {functorM : Functor M}
                                {monadM   : Monad M functorM}
                                {f g : A -> B}
                                (eq : (x : A) -> f x ≡ g x)
                                (d : DeltaM M {functorM} {monadM} A (S n)) ->
                                deltaM-fmap f d ≡ deltaM-fmap g d
{-
deltaM-fmap-equiv {n = O} f g eq (deltaM (mono x)) = begin
  {!!} ≡⟨ {!!} ⟩
  {!!}
  ∎
deltaM-fmap-equiv {n = S n} f g eq d = {!!}
-}

deltaM-is-functor : {l : Level} {n : Nat}
                                {M : Set l -> Set l}
                                {functorM : Functor M }
                                {monadM   : Monad M functorM}
                    -> Functor {l} (\A -> DeltaM M {functorM} {monadM} A (S n))
deltaM-is-functor {_} {_} {_} {functorM} = record { fmap         = deltaM-fmap ;
                                                    preserve-id  = deltaM-preserve-id functorM ;
                                                    covariant    = (\f g -> deltaM-covariant functorM g f);
                                                    fmap-equiv   = deltaM-fmap-equiv
                                                    }
