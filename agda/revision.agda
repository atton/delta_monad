open import Relation.Binary.PropositionalEquality
module revision where

data Rev : Set where
  init   : Rev
  commit : Rev -> Rev

merge : Rev -> Rev -> Rev
merge init b       = commit b
merge (commit a) b = commit (merge a b)

tip : Rev -> Rev -> Rev
tip init init             = init
tip init (commit b)       = commit b
tip (commit a) init       = commit a
tip (commit a) (commit b) = commit (tip a b)

open ≡-Reasoning

same-tip : (a : Rev) -> tip a a ≡ a
same-tip init       = refl
same-tip (commit v) = begin
     tip (commit v) (commit v) ≡⟨ refl ⟩
     commit (tip v v)          ≡⟨ cong commit (same-tip v) ⟩
     commit v                  ∎
