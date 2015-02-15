open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import basic
open import delta
open import delta.functor
open import nat
open import laws

module delta.monad where


tailDelta-to-tail-nt : {l : Level} {A B : Set l} (n m  : Nat)
                       (f : A -> B) (d : Delta (Delta A (S (S m))) (S n)) ->
                   delta-fmap tailDelta (delta-fmap (delta-fmap f) d) ≡ delta-fmap (delta-fmap f) (delta-fmap tailDelta d)
tailDelta-to-tail-nt O O f (mono (delta x d)) = refl
tailDelta-to-tail-nt O (S m) f (mono (delta x d)) = refl
tailDelta-to-tail-nt (S n) O f (delta (delta x (mono xx)) d) = begin
  delta (mono (f xx))
    (delta-fmap tailDelta (delta-fmap (delta-fmap f) d))
  ≡⟨ cong (\de -> delta (mono (f xx)) de) (tailDelta-to-tail-nt n O f d) ⟩
  delta (mono (f xx))
    (delta-fmap (delta-fmap f) (delta-fmap tailDelta d))
  ∎
tailDelta-to-tail-nt (S n) (S m) f (delta (delta x (delta xx d)) ds) = begin
  delta (delta (f xx) (delta-fmap f d))
    (delta-fmap tailDelta (delta-fmap (delta-fmap f) ds))
  ≡⟨ cong (\de -> delta (delta (f xx) (delta-fmap f d)) de) (tailDelta-to-tail-nt n (S m) f ds) ⟩
  delta (delta (f xx) (delta-fmap f d))
    (delta-fmap (delta-fmap f) (delta-fmap tailDelta ds))
  ∎


delta-eta-is-nt : {l : Level} {A B : Set l} -> {n : Nat}
                  (f : A -> B) -> (x : A) -> (delta-eta {n = n} ∙ f) x ≡ delta-fmap f (delta-eta x)
delta-eta-is-nt {n = O}   f x = refl
delta-eta-is-nt {n = S n} f x = begin
  (delta-eta ∙ f) x                        ≡⟨ refl ⟩
  delta-eta (f x)                          ≡⟨ refl ⟩
  delta (f x) (delta-eta (f x))            ≡⟨ cong (\de -> delta (f x) de) (delta-eta-is-nt f x) ⟩
  delta (f x) (delta-fmap f (delta-eta x)) ≡⟨ refl ⟩
  delta-fmap f (delta x (delta-eta x))     ≡⟨ refl ⟩
  delta-fmap f (delta-eta x)               ∎


delta-mu-is-nt : {l : Level} {A B : Set l} {n : Nat} -> (f : A -> B) -> (d : Delta (Delta A (S n)) (S n))
               -> delta-mu (delta-fmap (delta-fmap f) d) ≡ delta-fmap f (delta-mu d)
delta-mu-is-nt {n = O} f (mono d) = refl
delta-mu-is-nt {n = S n} f (delta (delta x d) ds) = begin
  delta (f x) (delta-mu (delta-fmap tailDelta (delta-fmap (delta-fmap f) ds)))
  ≡⟨ cong (\de -> delta (f x) (delta-mu de)) (tailDelta-to-tail-nt n n f ds ) ⟩
  delta (f x) (delta-mu (delta-fmap (delta-fmap f) (delta-fmap tailDelta ds)))
  ≡⟨ cong (\de -> delta (f x) de) (delta-mu-is-nt f (delta-fmap tailDelta ds)) ⟩
  delta (f x) (delta-fmap f (delta-mu (delta-fmap tailDelta ds)))
  ∎


delta-fmap-mu-to-tail : {l : Level} {A : Set l} (n m : Nat) (d : Delta (Delta (Delta A (S (S m))) (S (S m))) (S n)) ->
  delta-fmap tailDelta (delta-fmap delta-mu d)
  ≡
  (delta-fmap delta-mu (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta d)))
delta-fmap-mu-to-tail O O (mono (delta d ds)) = refl
delta-fmap-mu-to-tail O (S n) (mono (delta (delta x (delta xx d)) (delta (delta dx (delta dxx dd)) ds))) = refl
delta-fmap-mu-to-tail (S n) O (delta (delta (delta x (mono xx)) (mono (delta dx (mono dxx)))) ds) = begin
  delta (mono dxx) (delta-fmap tailDelta (delta-fmap delta-mu ds))
  ≡⟨ cong (\de -> delta (mono dxx) de) (delta-fmap-mu-to-tail n O ds) ⟩
  delta (mono dxx)
    (delta-fmap delta-mu
     (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta ds)))
  ∎
delta-fmap-mu-to-tail (S n) (S n₁) (delta (delta (delta x (delta xx d)) (delta (delta dx (delta dxx dd)) ds)) dds) = begin
  delta (delta dxx (delta-mu (delta-fmap tailDelta (delta-fmap tailDelta ds))))
    (delta-fmap tailDelta (delta-fmap delta-mu dds))
  ≡⟨ cong (\de -> delta (delta dxx (delta-mu (delta-fmap tailDelta (delta-fmap tailDelta ds)))) de) (delta-fmap-mu-to-tail n (S n₁) dds) ⟩
  delta (delta dxx (delta-mu (delta-fmap tailDelta (delta-fmap tailDelta ds))))
    (delta-fmap delta-mu (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta dds)))
  ∎



-- Monad-laws (Category)
-- association-law : join . delta-fmap join = join . join
delta-association-law : {l : Level} {A : Set l} {n : Nat} (d : Delta (Delta (Delta A (S n)) (S n)) (S n)) ->
              ((delta-mu ∙ (delta-fmap delta-mu)) d) ≡ ((delta-mu ∙ delta-mu) d)
delta-association-law {n =       O} (mono d)                          = refl
delta-association-law {n = S n} (delta (delta (delta x d) dd) ds) = begin
  delta x (delta-mu (delta-fmap tailDelta (delta-fmap delta-mu ds)))
  ≡⟨ cong (\de -> delta x (delta-mu de)) (delta-fmap-mu-to-tail n n ds) ⟩
  delta x (delta-mu (delta-fmap delta-mu (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta ds))))
  ≡⟨ cong (\de -> delta x de) (delta-association-law (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta ds))) ⟩
  delta x (delta-mu (delta-mu (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta ds))))
  ≡⟨ cong (\de -> delta x (delta-mu de)) (delta-mu-is-nt tailDelta (delta-fmap tailDelta ds) ) ⟩
  delta x (delta-mu (delta-fmap tailDelta (delta-mu (delta-fmap tailDelta ds))))
  ∎


delta-right-unity-law : {l : Level} {A : Set l} {n : Nat} (d : Delta A (S n)) -> (delta-mu ∙ delta-eta) d ≡ id d
delta-right-unity-law (mono x)    = refl
delta-right-unity-law (delta x d) = begin
  (delta-mu ∙ delta-eta) (delta x d)
  ≡⟨ refl ⟩
  delta-mu (delta-eta (delta x d))
  ≡⟨ refl ⟩
  delta-mu (delta (delta x d) (delta-eta (delta x d)))
  ≡⟨ refl ⟩
  delta (headDelta (delta x d)) (delta-mu (delta-fmap tailDelta (delta-eta (delta x d))))
  ≡⟨ refl ⟩
  delta x (delta-mu (delta-fmap tailDelta (delta-eta (delta x d))))
  ≡⟨ cong (\de -> delta x (delta-mu de)) (sym (delta-eta-is-nt  tailDelta (delta x d))) ⟩
  delta x (delta-mu (delta-eta (tailDelta (delta x d))))
  ≡⟨ refl ⟩
  delta x (delta-mu (delta-eta d))
  ≡⟨ cong (\de -> delta x de) (delta-right-unity-law d) ⟩
  delta x d
  ≡⟨ refl ⟩
  id (delta x d)  ∎


delta-left-unity-law  : {l : Level} {A : Set l} {n : Nat} -> (d : Delta A (S n)) ->
                                             (delta-mu  ∙ (delta-fmap delta-eta)) d ≡ id d
delta-left-unity-law (mono x)    = refl
delta-left-unity-law {n = (S n)} (delta x d) = begin
  (delta-mu ∙ delta-fmap delta-eta) (delta x d)            ≡⟨ refl ⟩
  delta-mu ( delta-fmap delta-eta (delta x d))             ≡⟨ refl ⟩
  delta-mu (delta (delta-eta x) (delta-fmap delta-eta d))  ≡⟨ refl ⟩
  delta (headDelta {n = S n} (delta-eta x)) (delta-mu (delta-fmap tailDelta (delta-fmap delta-eta d)))  ≡⟨ refl ⟩
  delta x (delta-mu (delta-fmap tailDelta (delta-fmap delta-eta d)))
  ≡⟨ cong (\de -> delta x (delta-mu de)) (sym (delta-covariant tailDelta delta-eta d)) ⟩
  delta x (delta-mu (delta-fmap (tailDelta ∙ delta-eta {n = S n}) d))  ≡⟨ refl ⟩
  delta x (delta-mu (delta-fmap (delta-eta {n = n}) d))  ≡⟨ cong (\de -> delta x de) (delta-left-unity-law d) ⟩
  delta x d ≡⟨ refl ⟩
  id (delta x d)  ∎



delta-is-monad : {l : Level} {n : Nat} -> Monad {l} (\A -> Delta A (S n))  delta-is-functor
delta-is-monad = record { eta    = delta-eta;
                          mu     = delta-mu;
                          eta-is-nt = delta-eta-is-nt;
                          mu-is-nt = delta-mu-is-nt;
                          association-law = delta-association-law;
                          left-unity-law  = delta-left-unity-law ;
                          right-unity-law = \x -> (sym (delta-right-unity-law x)) }





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
