open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import basic
open import delta
open import delta.functor
open import deltaM
open import laws
open Functor

module deltaM.functor where


deltaM-preserve-id :  {l : Level} {A : Set l}
                      {M : {l' : Level} -> Set l' -> Set l'}
                      (functorM : {l' : Level} -> Functor {l'} M)
                      {monadM   : {l' : Level} {A : Set l'} -> Monad {l'} {A} M functorM}
                      -> (d : DeltaM M {functorM} {monadM} A) -> (deltaM-fmap id) d ≡ id d
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

{-
deltaM-covariant : {l : Level} {A B C : Set l} ->
               (f : B -> C) -> (g : A -> B) -> (d : Delta A) ->
                (delta-fmap (f ∙ g)) d ≡ (delta-fmap f) (delta-fmap g d)
deltaM-covariant = {!!} 
-}