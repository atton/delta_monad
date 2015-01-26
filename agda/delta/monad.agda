open import basic
open import delta
open import delta.functor
open import nat
open import laws
open import revision


open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module delta.monad where


-- Monad-laws (Category)
{-

monad-law-1-5 : {l : Level} {A : Set l} -> (m : Nat) (n : Nat) -> (ds : Delta (Delta A)) ->
  n-tail n (delta-bind ds (n-tail m))  ≡ delta-bind (n-tail n ds) (n-tail (m + n))
monad-law-1-5 O O ds = refl
monad-law-1-5 O (S n) (mono ds) = begin
  n-tail (S n) (delta-bind (mono ds) (n-tail O))     ≡⟨ refl ⟩
  n-tail (S n) ds                              ≡⟨ refl ⟩
  delta-bind (mono ds) (n-tail (S n))                ≡⟨ cong (\de -> delta-bind de (n-tail (S n))) (sym (tail-delta-to-mono (S n) ds)) ⟩
  delta-bind (n-tail (S n) (mono ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (n-tail (S n) (mono ds)) (n-tail (O + S n))
  ∎
monad-law-1-5 O (S n) (delta d ds) = begin
  n-tail (S n) (delta-bind (delta d ds) (n-tail O))                         ≡⟨ refl ⟩
  n-tail (S n) (delta (headDelta d) (delta-bind ds tailDelta ))             ≡⟨ cong (\t -> t  (delta (headDelta d) (delta-bind ds tailDelta ))) (sym (n-tail-plus n)) ⟩
  ((n-tail n) ∙ tailDelta) (delta (headDelta d) (delta-bind ds tailDelta )) ≡⟨ refl ⟩
  (n-tail n) (delta-bind ds tailDelta)                                      ≡⟨ monad-law-1-5 (S O) n ds ⟩
  delta-bind (n-tail n ds) (n-tail  (S n))                                  ≡⟨ refl ⟩
  delta-bind (((n-tail n) ∙ tailDelta) (delta d ds)) (n-tail  (S n))        ≡⟨ cong (\t -> delta-bind (t (delta d ds)) (n-tail  (S n))) (n-tail-plus n) ⟩
  delta-bind (n-tail (S n) (delta d ds)) (n-tail  (S n))                    ≡⟨ refl ⟩
  delta-bind (n-tail (S n) (delta d ds)) (n-tail (O + S n))
  ∎
monad-law-1-5 (S m) n (mono (mono x)) = begin
  n-tail n (delta-bind (mono (mono x)) (n-tail (S m))) ≡⟨ refl ⟩
  n-tail n (n-tail (S m) (mono x))               ≡⟨ cong (\de -> n-tail n de) (tail-delta-to-mono (S m) x)⟩
  n-tail n (mono x)                              ≡⟨ tail-delta-to-mono n x ⟩
  mono x                                         ≡⟨ sym (tail-delta-to-mono (S m + n) x) ⟩
  (n-tail (S m + n)) (mono x)                    ≡⟨ refl ⟩
  delta-bind (mono (mono x)) (n-tail (S m + n))  ≡⟨ cong (\de -> delta-bind de (n-tail (S m + n))) (sym (tail-delta-to-mono n (mono x))) ⟩
  delta-bind (n-tail n (mono (mono x))) (n-tail (S m + n))
  ∎
monad-law-1-5 (S m) n (mono (delta x ds)) = begin
  n-tail n (delta-bind (mono (delta x ds)) (n-tail (S m))) ≡⟨ refl ⟩
  n-tail n (n-tail (S m) (delta x ds))               ≡⟨ cong (\t -> n-tail n (t (delta x ds))) (sym (n-tail-plus m)) ⟩
  n-tail n (((n-tail m) ∙ tailDelta) (delta x ds))   ≡⟨ refl ⟩
  n-tail n ((n-tail m) ds)                           ≡⟨ cong (\t -> t ds) (n-tail-add {d = ds} n m)  ⟩
  n-tail (n + m) ds                                  ≡⟨ cong (\n -> n-tail n ds) (nat-add-sym n m) ⟩
  n-tail (m + n) ds                                  ≡⟨ refl ⟩
  ((n-tail (m + n)) ∙ tailDelta) (delta x ds)        ≡⟨ cong (\t -> t (delta x ds)) (n-tail-plus (m + n))⟩
  n-tail (S (m + n)) (delta x ds)                    ≡⟨ refl ⟩
  n-tail (S m + n) (delta x ds)                      ≡⟨ refl ⟩
  delta-bind (mono (delta x ds)) (n-tail (S m + n))        ≡⟨ cong (\de -> delta-bind de (n-tail (S m + n))) (sym (tail-delta-to-mono n (delta x ds))) ⟩
  delta-bind (n-tail n (mono (delta x ds))) (n-tail (S m + n))
  ∎
monad-law-1-5 (S m) O (delta d ds) = begin
  n-tail O (delta-bind (delta d ds) (n-tail (S m)))                                 ≡⟨ refl ⟩
  (delta-bind (delta d ds) (n-tail (S m)))                                          ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S m)) d)) (delta-bind ds (tailDelta ∙ (n-tail (S m)))) ≡⟨ refl ⟩
  delta-bind (delta d ds) (n-tail (S m))                                            ≡⟨ refl ⟩
  delta-bind (n-tail O (delta d ds)) (n-tail (S m))                                 ≡⟨ cong (\n -> delta-bind (n-tail O (delta d ds)) (n-tail n)) (nat-add-right-zero (S m)) ⟩
  delta-bind (n-tail O (delta d ds)) (n-tail (S m + O))
  ∎
monad-law-1-5 (S m) (S n) (delta d ds) = begin
  n-tail (S n) (delta-bind (delta d ds) (n-tail (S m)))                                                         ≡⟨ cong (\t -> t ((delta-bind (delta d ds) (n-tail (S m))))) (sym (n-tail-plus n)) ⟩
  ((n-tail n) ∙ tailDelta) (delta-bind (delta d ds) (n-tail (S m)))                                             ≡⟨ refl ⟩
  ((n-tail n) ∙ tailDelta) (delta (headDelta ((n-tail (S m)) d)) (delta-bind ds (tailDelta ∙  (n-tail (S m))))) ≡⟨ refl ⟩
  (n-tail n) (delta-bind ds (tailDelta ∙ (n-tail (S m))))                                                       ≡⟨ refl ⟩
  (n-tail n) (delta-bind ds (n-tail (S (S m))))                                                                 ≡⟨ monad-law-1-5 (S (S m)) n ds ⟩
  delta-bind ((n-tail n) ds) (n-tail (S (S (m + n))))                                                           ≡⟨ cong (\nm -> delta-bind ((n-tail n) ds) (n-tail nm))  (sym (nat-right-increment (S m) n)) ⟩
  delta-bind ((n-tail n) ds) (n-tail (S m + S n))                                                               ≡⟨ refl ⟩
  delta-bind (((n-tail n) ∙ tailDelta) (delta d ds)) (n-tail (S m + S n))                                       ≡⟨ cong (\t -> delta-bind (t (delta d ds)) (n-tail (S m + S n))) (n-tail-plus n) ⟩
  delta-bind (n-tail (S n) (delta d ds)) (n-tail (S m + S n))
  ∎

monad-law-1-4 : {l : Level} {A : Set l} -> (m n : Nat) -> (dd : Delta (Delta A)) ->
  headDelta ((n-tail n) (delta-bind dd (n-tail m))) ≡ headDelta ((n-tail (m + n)) (headDelta (n-tail n dd)))
monad-law-1-4 O O (mono dd) = refl
monad-law-1-4 O O (delta dd dd₁) = refl
monad-law-1-4 O (S n) (mono dd) = begin
  headDelta (n-tail (S n) (delta-bind (mono dd) (n-tail O)))    ≡⟨ refl ⟩
  headDelta (n-tail (S n) dd)                                   ≡⟨ refl ⟩
  headDelta (n-tail (S n) (headDelta (mono dd)))                ≡⟨ cong (\de -> headDelta (n-tail (S n) (headDelta de))) (sym (tail-delta-to-mono (S n) dd)) ⟩
  headDelta (n-tail (S n) (headDelta (n-tail (S n) (mono dd)))) ≡⟨ refl ⟩
  headDelta (n-tail (O + S n) (headDelta (n-tail (S n) (mono dd))))
  ∎
monad-law-1-4 O (S n) (delta d ds) = begin
  headDelta (n-tail (S n) (delta-bind (delta d ds) (n-tail O)))                        ≡⟨ refl ⟩
  headDelta (n-tail (S n) (delta-bind (delta d ds) id))                                ≡⟨ refl ⟩
  headDelta (n-tail (S n) (delta (headDelta d) (delta-bind ds tailDelta)))             ≡⟨ cong (\t -> headDelta (t (delta (headDelta d) (delta-bind ds tailDelta)))) (sym (n-tail-plus n)) ⟩
  headDelta (((n-tail n) ∙ tailDelta) (delta (headDelta d) (delta-bind ds tailDelta))) ≡⟨ refl ⟩
  headDelta (n-tail n (delta-bind ds tailDelta))                                       ≡⟨ monad-law-1-4 (S O) n ds ⟩
  headDelta (n-tail (S n) (headDelta (n-tail n ds)))                                   ≡⟨ refl ⟩
  headDelta (n-tail (S n) (headDelta (((n-tail n) ∙ tailDelta) (delta d ds))))         ≡⟨ cong (\t -> headDelta (n-tail (S n) (headDelta (t (delta d ds))))) (n-tail-plus n)  ⟩
  headDelta (n-tail (S n) (headDelta (n-tail (S n) (delta d ds))))                     ≡⟨ refl ⟩
  headDelta (n-tail (O + S n) (headDelta (n-tail (S n) (delta d ds))))
  ∎
monad-law-1-4 (S m) n (mono dd) = begin
  headDelta (n-tail n (delta-bind (mono dd) (n-tail (S m)))) ≡⟨ refl ⟩
  headDelta (n-tail n ((n-tail (S m)) dd))                   ≡⟨ cong (\t -> headDelta (t dd)) (n-tail-add {d = dd} n (S m)) ⟩
  headDelta (n-tail (n + S m) dd)                            ≡⟨ cong (\n -> headDelta ((n-tail n) dd)) (nat-add-sym n (S m)) ⟩
  headDelta (n-tail (S m + n) dd)                            ≡⟨ refl ⟩
  headDelta (n-tail (S m + n) (headDelta (mono dd)))         ≡⟨ cong (\de -> headDelta (n-tail (S m + n) (headDelta de))) (sym (tail-delta-to-mono n dd)) ⟩
  headDelta (n-tail (S m + n) (headDelta (n-tail n (mono dd))))
  ∎
monad-law-1-4 (S m) O (delta d ds) = begin
  headDelta (n-tail O (delta-bind (delta d ds) (n-tail (S m))))                                 ≡⟨ refl ⟩
  headDelta (delta-bind (delta d ds) (n-tail (S m)))                                            ≡⟨ refl ⟩
  headDelta (delta (headDelta ((n-tail (S m) d))) (delta-bind ds (tailDelta ∙ (n-tail (S m))))) ≡⟨ refl ⟩
  headDelta (n-tail (S m) d)                                                              ≡⟨ cong (\n -> headDelta ((n-tail n) d)) (nat-add-right-zero (S m)) ⟩
  headDelta (n-tail (S m + O) d)                                                          ≡⟨ refl ⟩
  headDelta (n-tail (S m + O) (headDelta (delta d ds)))                                   ≡⟨ refl ⟩
  headDelta (n-tail (S m + O) (headDelta (n-tail O (delta d ds))))
  ∎
monad-law-1-4 (S m) (S n) (delta d ds) = begin
  headDelta (n-tail (S n) (delta-bind (delta d ds) (n-tail (S m))))                                                          ≡⟨ refl ⟩
  headDelta (n-tail (S n) (delta (headDelta ((n-tail (S m)) d)) (delta-bind ds (tailDelta ∙ (n-tail (S m))))))               ≡⟨ cong (\t -> headDelta (t (delta (headDelta ((n-tail (S m)) d)) (delta-bind ds (tailDelta ∙ (n-tail (S m))))))) (sym (n-tail-plus n)) ⟩
  headDelta ((((n-tail n) ∙ tailDelta) (delta (headDelta ((n-tail (S m)) d)) (delta-bind ds (tailDelta ∙ (n-tail (S m))))))) ≡⟨ refl ⟩
  headDelta (n-tail n (delta-bind ds (tailDelta ∙ (n-tail (S m)))))                                                          ≡⟨ refl ⟩
  headDelta (n-tail n (delta-bind ds  (n-tail (S (S m)))))                                                                   ≡⟨ monad-law-1-4 (S (S m)) n ds ⟩
  headDelta (n-tail ((S (S m) +  n)) (headDelta (n-tail n ds)))                                                        ≡⟨ cong (\nm -> headDelta ((n-tail nm) (headDelta (n-tail n ds)))) (sym (nat-right-increment (S m) n))  ⟩
  headDelta (n-tail (S m + S n) (headDelta (n-tail n ds)))                                                             ≡⟨ refl ⟩
  headDelta (n-tail (S m + S n) (headDelta (((n-tail n) ∙ tailDelta) (delta d ds))))                                   ≡⟨ cong (\t -> headDelta (n-tail (S m + S n) (headDelta (t (delta d ds))))) (n-tail-plus n) ⟩
  headDelta (n-tail (S m + S n) (headDelta (n-tail (S n) (delta d ds))))
  ∎

monad-law-1-2 : {l : Level} {A : Set l} -> (d : Delta (Delta A)) -> headDelta (delta-mu d) ≡ (headDelta (headDelta d))
monad-law-1-2 (mono _)    = refl
monad-law-1-2 (delta _ _) = refl

monad-law-1-3 : {l : Level} {A : Set l} -> (n : Nat) -> (d : Delta (Delta (Delta A))) ->
  delta-bind (delta-fmap delta-mu d) (n-tail n) ≡ delta-bind (delta-bind d (n-tail n)) (n-tail n)
monad-law-1-3 O (mono d)     = refl
monad-law-1-3 O (delta d ds) = begin
  delta-bind (delta-fmap delta-mu (delta d ds)) (n-tail O)                               ≡⟨ refl ⟩
  delta-bind (delta (delta-mu d) (delta-fmap delta-mu ds)) (n-tail O)                          ≡⟨ refl ⟩
  delta (headDelta (delta-mu d)) (delta-bind (delta-fmap delta-mu ds) tailDelta)               ≡⟨ cong (\dx -> delta dx (delta-bind (delta-fmap delta-mu ds) tailDelta)) (monad-law-1-2 d) ⟩
  delta (headDelta (headDelta d)) (delta-bind (delta-fmap delta-mu ds) tailDelta)        ≡⟨ cong (\dx -> delta (headDelta (headDelta d)) dx) (monad-law-1-3 (S O) ds) ⟩
  delta (headDelta (headDelta d)) (delta-bind (delta-bind ds tailDelta) tailDelta) ≡⟨ refl ⟩
  delta-bind (delta (headDelta d) (delta-bind ds tailDelta)) (n-tail O)            ≡⟨ refl ⟩
  delta-bind (delta-bind (delta d ds) (n-tail O)) (n-tail O)
  ∎
monad-law-1-3 (S n) (mono (mono d)) = begin
  delta-bind (delta-fmap delta-mu (mono (mono d))) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (mono d) (n-tail (S n))                  ≡⟨ refl ⟩
  (n-tail (S n)) d                              ≡⟨ refl ⟩
  delta-bind (mono d) (n-tail (S n))                  ≡⟨ cong (\t -> delta-bind t (n-tail (S n))) (sym (tail-delta-to-mono (S n) d))⟩
  delta-bind (n-tail (S n) (mono d)) (n-tail (S n))   ≡⟨ refl ⟩
  delta-bind (n-tail (S n) (mono d)) (n-tail (S n))   ≡⟨ refl ⟩
  delta-bind (delta-bind (mono (mono d)) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (mono (delta d ds)) = begin
  delta-bind (delta-fmap delta-mu (mono (delta d ds))) (n-tail (S n))                ≡⟨ refl ⟩
  delta-bind (mono (delta-mu (delta d ds))) (n-tail (S n))                     ≡⟨ refl ⟩
  n-tail (S n) (delta-mu (delta d ds))                                   ≡⟨ refl ⟩
  n-tail (S n) (delta (headDelta d) (delta-bind ds tailDelta))           ≡⟨ cong (\t -> t (delta (headDelta d) (delta-bind ds tailDelta))) (sym (n-tail-plus n)) ⟩
  (n-tail n ∙ tailDelta) (delta (headDelta d) (delta-bind ds tailDelta)) ≡⟨ refl ⟩
  n-tail n (delta-bind ds tailDelta)                                     ≡⟨ monad-law-1-5 (S O) n ds ⟩
  delta-bind (n-tail n ds) (n-tail (S n))                                ≡⟨ refl ⟩
  delta-bind (((n-tail n) ∙ tailDelta) (delta d ds)) (n-tail (S n))      ≡⟨ cong (\t -> (delta-bind (t (delta d ds)) (n-tail (S n))))  (n-tail-plus n) ⟩
  delta-bind (n-tail (S n) (delta d ds)) (n-tail (S n))                  ≡⟨ refl ⟩
  delta-bind (delta-bind (mono (delta d ds)) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (delta (mono d) ds) = begin
  delta-bind (delta-fmap delta-mu (delta (mono d) ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (delta (delta-mu (mono d)) (delta-fmap delta-mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (delta d (delta-fmap delta-mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (delta-bind (delta-fmap delta-mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (delta-bind (delta-fmap delta-mu ds) (n-tail (S (S n)))) ≡⟨ cong (\de -> delta (headDelta ((n-tail (S n)) d)) de) (monad-law-1-3 (S (S n)) ds) ⟩
  delta (headDelta ((n-tail (S n)) d)) (delta-bind (delta-bind ds (n-tail (S (S n)))) (n-tail (S (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (delta-bind (delta-bind ds (tailDelta ∙ (n-tail (S n))))  (n-tail (S (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (delta-bind (delta-bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (mono d)))) (delta-bind (delta-bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ cong (\de -> delta (headDelta ((n-tail (S n)) (headDelta de))) (delta-bind (delta-bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n))))) (sym (tail-delta-to-mono (S n) d)) ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) (mono d))))) (delta-bind (delta-bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ refl ⟩
  delta-bind (delta (headDelta ((n-tail (S n)) (mono d))) (delta-bind ds (tailDelta ∙ (n-tail (S n))))) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (delta-bind (delta (mono d) ds) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (delta (delta d dd) ds) = begin
  delta-bind (delta-fmap delta-mu (delta (delta d dd) ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (delta (delta-mu (delta d dd)) (delta-fmap delta-mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (delta-mu (delta d dd)))) (delta-bind (delta-fmap delta-mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (delta (headDelta d) (delta-bind dd tailDelta)))) (delta-bind (delta-fmap delta-mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ cong (\t -> delta (headDelta (t (delta (headDelta d) (delta-bind dd tailDelta)))) (delta-bind (delta-fmap delta-mu ds) (tailDelta ∙ (n-tail (S n)))))(sym (n-tail-plus n)) ⟩
  delta (headDelta (((n-tail n) ∙ tailDelta) (delta (headDelta d) (delta-bind dd tailDelta)))) (delta-bind (delta-fmap delta-mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail n) (delta-bind dd tailDelta))) (delta-bind (delta-fmap delta-mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail n) (delta-bind dd tailDelta))) (delta-bind (delta-fmap delta-mu ds) (n-tail (S (S n)))) ≡⟨ cong (\de -> delta (headDelta ((n-tail n) (delta-bind dd tailDelta))) de) (monad-law-1-3 (S (S n)) ds) ⟩
  delta (headDelta ((n-tail n) (delta-bind dd tailDelta))) (delta-bind (delta-bind  ds (n-tail (S (S n))))  (n-tail (S (S n)))) ≡⟨ cong (\de -> delta de ( (delta-bind (delta-bind  ds (n-tail (S (S n))))  (n-tail (S (S n)))))) (monad-law-1-4 (S O) n dd) ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (n-tail n dd)))) (delta-bind (delta-bind  ds (n-tail (S (S n))))  (n-tail (S (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (n-tail n dd)))) (delta-bind (delta-bind  ds (n-tail (S (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (n-tail n dd)))) (delta-bind (delta-bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (((n-tail n) ∙ tailDelta) (delta d dd))))) (delta-bind (delta-bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ cong (\t -> delta (headDelta ((n-tail (S n)) (headDelta (t (delta d dd))))) (delta-bind (delta-bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n))))) (n-tail-plus n) ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) (delta d dd))))) (delta-bind (delta-bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta-bind (delta (headDelta ((n-tail (S n)) (delta d dd))) (delta-bind  ds (tailDelta ∙ (n-tail (S n))))) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (delta-bind (delta (delta d dd) ds) (n-tail (S n))) (n-tail (S n))
  ∎


-- monad-law-1 : join . delta-fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((delta-mu ∙ (delta-fmap delta-mu)) d) ≡ ((delta-mu ∙ delta-mu) d)
monad-law-1 (mono d)    = refl
monad-law-1 (delta x d) = begin
  (delta-mu ∙ delta-fmap delta-mu) (delta x d)                                          ≡⟨ refl ⟩
  delta-mu (delta-fmap delta-mu (delta x d))                                            ≡⟨ refl ⟩
  delta-mu (delta (delta-mu x) (delta-fmap delta-mu d))                                       ≡⟨ refl ⟩
  delta (headDelta (delta-mu x)) (delta-bind (delta-fmap delta-mu d) tailDelta)               ≡⟨ cong (\x -> delta x (delta-bind (delta-fmap delta-mu d) tailDelta)) (monad-law-1-2 x) ⟩
  delta (headDelta (headDelta x)) (delta-bind (delta-fmap delta-mu d) tailDelta)        ≡⟨ cong (\d -> delta (headDelta (headDelta x)) d) (monad-law-1-3 (S O) d) ⟩
  delta (headDelta (headDelta x)) (delta-bind (delta-bind d tailDelta) tailDelta) ≡⟨ refl ⟩
  delta-mu (delta (headDelta x) (delta-bind d tailDelta))                         ≡⟨ refl ⟩
  delta-mu (delta-mu (delta x d))                                                 ≡⟨ refl ⟩
  (delta-mu ∙ delta-mu) (delta x d)
  ∎


monad-law-2-1 : {l : Level} {A : Set l} -> (n : Nat) -> (d : Delta A) -> (delta-bind (delta-fmap delta-eta d) (n-tail n)) ≡ d
monad-law-2-1 O (mono x)    = refl
monad-law-2-1 O (delta x d) = begin
  delta-bind (delta-fmap delta-eta (delta x d)) (n-tail O)                  ≡⟨ refl ⟩
  delta-bind (delta (delta-eta x) (delta-fmap delta-eta d)) id                    ≡⟨ refl ⟩
  delta (headDelta (delta-eta x)) (delta-bind (delta-fmap delta-eta d) tailDelta) ≡⟨ refl ⟩
  delta x (delta-bind (delta-fmap delta-eta d) tailDelta)                   ≡⟨ cong (\de -> delta x de) (monad-law-2-1 (S O) d) ⟩
  delta x d                                               ∎
monad-law-2-1 (S n) (mono x) = begin
  delta-bind (delta-fmap delta-eta (mono x)) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (mono (mono x)) (n-tail (S n))     ≡⟨ refl ⟩
  n-tail (S n) (mono x)                   ≡⟨ tail-delta-to-mono (S n) x ⟩
  mono x                                  ∎
monad-law-2-1 (S n) (delta x d) = begin
  delta-bind (delta-fmap delta-eta (delta x d)) (n-tail (S n))                                                   ≡⟨ refl ⟩
  delta-bind (delta (delta-eta x) (delta-fmap delta-eta d)) (n-tail (S n))                                             ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n) (delta-eta x)))) (delta-bind (delta-fmap delta-eta d) (tailDelta ∙  (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n) (delta-eta x)))) (delta-bind (delta-fmap delta-eta d) (n-tail (S (S n))))            ≡⟨ cong (\de -> delta (headDelta (de)) (delta-bind (delta-fmap delta-eta d) (n-tail (S (S n))))) (tail-delta-to-mono (S n) x) ⟩
  delta (headDelta (delta-eta x)) (delta-bind (delta-fmap delta-eta d) (n-tail (S (S n))))                             ≡⟨ refl ⟩
  delta x (delta-bind (delta-fmap delta-eta d) (n-tail (S (S n))))                                               ≡⟨ cong (\d -> delta x d) (monad-law-2-1 (S (S n)) d) ⟩
  delta x d
  ∎


-- monad-law-2 : join . delta-fmap return = join . return = id
-- monad-law-2 join . delta-fmap return = join . return
monad-law-2 : {l : Level} {A : Set l} -> (d : Delta A) ->
  (delta-mu ∙ delta-fmap delta-eta) d ≡ (delta-mu ∙ delta-eta) d
monad-law-2 (mono x)    = refl
monad-law-2 (delta x d) = begin
  (delta-mu ∙ delta-fmap delta-eta) (delta x d)                              ≡⟨ refl ⟩
  delta-mu (delta-fmap delta-eta (delta x d))                                ≡⟨ refl ⟩
  delta-mu (delta (mono x) (delta-fmap delta-eta d))                         ≡⟨ refl ⟩
  delta (headDelta (mono x)) (delta-bind (delta-fmap delta-eta d) tailDelta) ≡⟨ refl ⟩
  delta x (delta-bind (delta-fmap delta-eta d) tailDelta)                    ≡⟨ cong (\d -> delta x d) (monad-law-2-1 (S O) d) ⟩
  (delta x d)                                              ≡⟨ refl ⟩
  delta-mu (mono (delta x d))                                    ≡⟨ refl ⟩
  delta-mu (delta-eta (delta x d))                                     ≡⟨ refl ⟩
  (delta-mu ∙ delta-eta) (delta x d)
  ∎


-- monad-law-2' :  join . return = id
monad-law-2' : {l : Level} {A : Set l} -> (d : Delta A) -> (delta-mu ∙ delta-eta) d ≡ id d
monad-law-2' d = refl


-- monad-law-3 : return . f = delta-fmap f . return
monad-law-3 : {l : Level} {A B : Set l} (f : A -> B) (x : A) -> (delta-eta ∙ f) x ≡ (delta-fmap f ∙ delta-eta) x
monad-law-3 f x = refl


monad-law-4-1 : {l  : Level} {A B : Set l} -> (n : Nat) -> (f : A -> B) -> (ds : Delta (Delta A)) ->
  delta-bind (delta-fmap (delta-fmap f) ds) (n-tail n) ≡ delta-fmap f (delta-bind ds (n-tail n))
monad-law-4-1 O f (mono d)     = refl
monad-law-4-1 O f (delta d ds) = begin
  delta-bind (delta-fmap (delta-fmap f) (delta d ds)) (n-tail O)                     ≡⟨ refl ⟩
  delta-bind (delta (delta-fmap f d) (delta-fmap (delta-fmap f) ds)) (n-tail O)            ≡⟨ refl ⟩
  delta (headDelta (delta-fmap f d)) (delta-bind (delta-fmap (delta-fmap f) ds) tailDelta) ≡⟨ cong (\de -> delta de (delta-bind (delta-fmap (delta-fmap f) ds) tailDelta)) (head-delta-natural-transformation f d) ⟩
  delta (f (headDelta d))      (delta-bind (delta-fmap (delta-fmap f) ds) tailDelta) ≡⟨ cong (\de -> delta (f (headDelta d)) de) (monad-law-4-1 (S O) f ds) ⟩
  delta (f (headDelta d))      (delta-fmap f (delta-bind ds tailDelta))        ≡⟨ refl ⟩
  delta-fmap f (delta (headDelta d) (delta-bind ds tailDelta))                 ≡⟨ refl ⟩
  delta-fmap f (delta-bind (delta d ds) (n-tail O))                            ∎
monad-law-4-1 (S n) f (mono d) = begin
  delta-bind (delta-fmap (delta-fmap f) (mono d)) (n-tail (S n)) ≡⟨ refl ⟩
  delta-bind (mono (delta-fmap f d)) (n-tail (S n))        ≡⟨ refl ⟩
  n-tail (S n) (delta-fmap f d)                      ≡⟨ n-tail-natural-transformation (S n) f d ⟩
  delta-fmap f (n-tail (S n) d)                      ≡⟨ refl ⟩
  delta-fmap f (delta-bind (mono d) (n-tail (S n)))
  ∎
monad-law-4-1 (S n) f (delta d ds) = begin
  delta-bind (delta-fmap (delta-fmap f) (delta d ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta (n-tail (S n) (delta-fmap f d))) (delta-bind (delta-fmap (delta-fmap f) ds) (tailDelta ∙ (n-tail (S n))))  ≡⟨ refl ⟩
  delta (headDelta (n-tail (S n) (delta-fmap f d))) (delta-bind (delta-fmap (delta-fmap f) ds) (n-tail (S (S n))))            ≡⟨ cong (\de ->   delta (headDelta de) (delta-bind (delta-fmap (delta-fmap f) ds) (n-tail (S (S n))))) (n-tail-natural-transformation (S n) f d) ⟩
  delta (headDelta (delta-fmap f ((n-tail (S n) d)))) (delta-bind (delta-fmap (delta-fmap f) ds) (n-tail (S (S n))))          ≡⟨ cong (\de -> delta de (delta-bind (delta-fmap (delta-fmap f) ds) (n-tail (S (S n))))) (head-delta-natural-transformation f (n-tail (S n) d)) ⟩
  delta (f (headDelta (n-tail (S n) d))) (delta-bind (delta-fmap (delta-fmap f) ds) (n-tail (S (S n))))                 ≡⟨ cong (\de -> delta (f (headDelta (n-tail (S n) d))) de) (monad-law-4-1 (S (S n)) f ds) ⟩
  delta (f (headDelta (n-tail (S n) d))) (delta-fmap f (delta-bind ds (n-tail (S (S n)))))                        ≡⟨ refl ⟩
  delta-fmap f (delta (headDelta (n-tail (S n) d)) (delta-bind ds (n-tail (S (S n)))))                            ≡⟨ refl ⟩
  delta-fmap f (delta (headDelta (n-tail (S n) d)) (delta-bind ds (tailDelta ∙ (n-tail (S n)))))                  ≡⟨ refl ⟩
  delta-fmap f (delta-bind (delta d ds) (n-tail (S n)))                                                           ∎


-- monad-law-4 : join . delta-fmap (delta-fmap f) = delta-fmap f . join
monad-law-4 : {l : Level} {A B : Set l} (f : A -> B) (d : Delta (Delta A)) ->
              (delta-mu ∙ delta-fmap (delta-fmap f)) d ≡ (delta-fmap f ∙ delta-mu) d
monad-law-4 f (mono d)     = refl
monad-law-4 f (delta (mono x) ds) = begin
  (delta-mu ∙ delta-fmap (delta-fmap f)) (delta (mono x) ds)                           ≡⟨ refl ⟩
  delta-mu ( delta-fmap (delta-fmap f) (delta (mono x) ds))                            ≡⟨ refl ⟩
  delta-mu (delta (mono (f x)) (delta-fmap (delta-fmap f) ds))                         ≡⟨ refl ⟩
  delta (headDelta (mono (f x))) (delta-bind (delta-fmap (delta-fmap f) ds) tailDelta) ≡⟨ refl ⟩
  delta (f x) (delta-bind (delta-fmap (delta-fmap f) ds) tailDelta)                    ≡⟨ cong (\de -> delta (f x) de) (monad-law-4-1 (S O) f ds) ⟩
  delta (f x) (delta-fmap f (delta-bind ds tailDelta))                           ≡⟨ refl ⟩
  delta-fmap f (delta x (delta-bind ds tailDelta))                               ≡⟨ refl ⟩
  delta-fmap f (delta (headDelta (mono x)) (delta-bind ds tailDelta))            ≡⟨ refl ⟩
  delta-fmap f (delta-mu (delta (mono x) ds))                                    ≡⟨ refl ⟩
  (delta-fmap f ∙ delta-mu) (delta (mono x) ds)                                  ∎
monad-law-4 f (delta (delta x d) ds) = begin
  (delta-mu ∙ delta-fmap (delta-fmap f)) (delta (delta x d) ds)                                     ≡⟨ refl ⟩
  delta-mu (delta-fmap (delta-fmap f) (delta (delta x d) ds))                                       ≡⟨ refl ⟩
  delta-mu  (delta (delta (f x) (delta-fmap f d)) (delta-fmap (delta-fmap f) ds))                         ≡⟨ refl ⟩
  delta (headDelta (delta (f x) (delta-fmap f d)))  (delta-bind (delta-fmap (delta-fmap f) ds) tailDelta) ≡⟨ refl ⟩
  delta (f x)  (delta-bind (delta-fmap (delta-fmap f) ds) tailDelta)                                ≡⟨ cong (\de -> delta (f x) de) (monad-law-4-1 (S O) f ds) ⟩
  delta (f x) (delta-fmap f (delta-bind  ds tailDelta))                                       ≡⟨ refl ⟩
  delta-fmap f (delta x (delta-bind  ds tailDelta))                                           ≡⟨ refl ⟩
  delta-fmap f (delta (headDelta (delta x d)) (delta-bind  ds tailDelta))                     ≡⟨ refl ⟩
  delta-fmap f (delta-mu (delta (delta x d) ds))                                              ≡⟨ refl ⟩
  (delta-fmap f ∙ delta-mu) (delta (delta x d) ds) ∎

-}
-- monad-law-1 : join . delta-fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} {a : Rev} -> (d : Delta (Delta (Delta A a) a) a) ->
            ((delta-mu ∙ (delta-fmap delta-mu)) d) ≡ ((delta-mu ∙ delta-mu) d)
monad-law-1 (mono d)     = refl
monad-law-1 (delta d ds) = {!!}

delta-is-monad : {l : Level} {v : Rev} -> Monad {l} (\A -> Delta A v)  delta-is-functor


delta-is-monad = record { eta    = delta-eta;
                          mu     = delta-mu;
                          return = delta-eta;
                          bind   = delta-bind;
                          association-law = monad-law-1 }
--                          left-unity-law  = monad-law-2;
--                          right-unity-law = monad-law-2' }





{-

-- Monad-laws (Haskell)
-- monad-law-h-1 : return a >>= k  =  k a
monad-law-h-1 : {l : Level} {A B : Set l} -> 
                (a : A) -> (k : A -> (Delta B)) ->
                (delta-return a >>= k)  ≡ (k a)
monad-law-h-1 a k = refl



-- monad-law-h-2 : m >>= return  =  m
monad-law-h-2 : {l : Level}{A : Set l} -> (m : Delta A) -> (m >>= delta-return)  ≡ m
monad-law-h-2 (mono x)    = refl
monad-law-h-2 (delta x d) = cong (delta x) (monad-law-h-2 d)



-- monad-law-h-3 : m >>= (\x -> f x >>= g)  =  (m >>= f) >>= g
monad-law-h-3 : {l : Level} {A B C : Set l} -> 
                (m : Delta A)  -> (f : A -> (Delta B)) -> (g : B -> (Delta C)) ->
                (delta-bind m (\x -> delta-bind (f x) g)) ≡ (delta-bind (delta-bind m f) g)
monad-law-h-3 (mono x) f g     = refl
monad-law-h-3 (delta x d) f g = begin
  (delta-bind (delta x d) (\x -> delta-bind (f x) g)) ≡⟨ {!!} ⟩
  (delta-bind (delta-bind (delta x d) f) g) ∎




-}