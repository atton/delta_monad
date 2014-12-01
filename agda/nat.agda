open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module nat where

data Nat : Set where
  O  : Nat
  S : Nat -> Nat

_+_ : Nat -> Nat -> Nat
O + n = n
(S m) + n = S (m + n)

nat-add-right-zero : (n : Nat) -> n  ≡ n + O
nat-add-right-zero O     = refl
nat-add-right-zero (S n) = begin
  S n       ≡⟨ cong (\n -> S n) (nat-add-right-zero n) ⟩
  S (n + O) ≡⟨ refl ⟩
  S n + O
  ∎

nat-right-increment : (n m : Nat) -> n + S m ≡ S (n + m)
nat-right-increment O m     = refl
nat-right-increment (S n) m = cong S (nat-right-increment n m) 

nat-add-sym : (n m : Nat) -> n + m ≡ m + n
nat-add-sym O O         = refl
nat-add-sym O (S m)     = cong S (nat-add-sym O m)
nat-add-sym (S n) O     = cong S (nat-add-sym n O)
nat-add-sym (S n) (S m) = begin
  S n + S m     ≡⟨ refl ⟩
  S (n + S m)   ≡⟨ cong S (nat-add-sym n (S m)) ⟩
  S ((S m) + n) ≡⟨ sym (nat-right-increment (S m) n) ⟩
  S m + S n     ∎
