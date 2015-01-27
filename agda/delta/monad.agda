open import basic
open import delta
open import delta.functor
open import nat
open import laws


open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module delta.monad where

delta-eta-is-nt : {l : Level} {A B : Set l} -> {n : Nat}
                  (f : A -> B) -> (x : A) -> (delta-eta {n = n} ∙ f) x ≡ delta-fmap f (delta-eta x)
delta-eta-is-nt {n = O}   f x = refl
delta-eta-is-nt {n = S O} f x = refl
delta-eta-is-nt {n = S n} f x = begin
  (delta-eta ∙ f) x                        ≡⟨ refl ⟩
  delta-eta (f x)                          ≡⟨ refl ⟩
  delta (f x) (delta-eta (f x))            ≡⟨ cong (\de -> delta (f x) de) (delta-eta-is-nt f x) ⟩
  delta (f x) (delta-fmap f (delta-eta x)) ≡⟨ refl ⟩
  delta-fmap f (delta x (delta-eta x))     ≡⟨ refl ⟩
  delta-fmap f (delta-eta x)               ∎

delta-mu-is-nt : {l : Level} {A B : Set l} {n : Nat} -> (f : A -> B) -> (d : Delta (Delta A (S n)) (S n))
               -> delta-mu (delta-fmap (delta-fmap f) d) ≡ delta-fmap f (delta-mu d)
delta-mu-is-nt f d = {!!}

hoge : {l : Level} {A : Set l} {n : Nat} -> (ds : Delta (Delta A (S (S n))) (S (S n))) ->
  (tailDelta {n = n} ∙ delta-mu {n = (S n)}) ds
  ≡
  (((delta-mu {n = n}) ∙ (delta-fmap tailDelta)) ∙ tailDelta) ds
hoge (delta ds ds₁) = refl




-- Monad-laws (Category)
-- monad-law-1 : join . delta-fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} {n : Nat} (d : Delta (Delta (Delta A (S n)) (S n)) (S n)) ->
              ((delta-mu ∙ (delta-fmap delta-mu)) d) ≡ ((delta-mu ∙ delta-mu) d)
monad-law-1 {n =   O} (mono d)     = refl
monad-law-1 {n = S O} (delta (delta (delta _ _) _) (mono (delta (delta _ (mono _)) (mono (delta _ (mono _)))))) = refl
monad-law-1 {n = S n} (delta (delta (delta x d) dd) ds) = begin
  (delta-mu ∙ delta-fmap delta-mu) (delta (delta (delta x d) dd) ds) ≡⟨ refl ⟩
  delta-mu (delta-fmap delta-mu (delta (delta (delta x d) dd) ds)) ≡⟨ refl ⟩
  delta-mu (delta (delta-mu (delta (delta x d) dd)) (delta-fmap delta-mu ds)) ≡⟨ refl ⟩
  delta-mu (delta (delta (headDelta (delta x d)) (delta-mu (delta-fmap tailDelta dd))) (delta-fmap delta-mu ds)) ≡⟨ refl ⟩
  delta-mu (delta (delta x (delta-mu (delta-fmap tailDelta dd))) (delta-fmap delta-mu ds)) ≡⟨ refl ⟩
  delta (headDelta (delta x (delta-mu (delta-fmap tailDelta dd)))) (delta-mu (delta-fmap tailDelta (delta-fmap delta-mu ds))) ≡⟨ refl ⟩
  delta x (delta-mu (delta-fmap tailDelta (delta-fmap delta-mu ds)))
  ≡⟨ cong (\de -> delta x (delta-mu de)) (sym (functor-law-2 tailDelta delta-mu ds)) ⟩
  delta x (delta-mu (delta-fmap (tailDelta {n = n} ∙ delta-mu {n = (S n)}) ds))
--  ≡⟨ cong (\ff -> delta x (delta-mu (delta-fmap ff ds))) hoge ⟩
  ≡⟨ {!!} ⟩
  delta x (delta-mu (delta-fmap (((delta-mu {n = n}) ∙ (delta-fmap tailDelta)) ∙ tailDelta) ds))
  ≡⟨ cong (\de -> delta x (delta-mu de)) (functor-law-2 (delta-mu ∙ (delta-fmap tailDelta)) tailDelta ds ) ⟩
  delta x (delta-mu (delta-fmap ((delta-mu {n = n}) ∙ (delta-fmap tailDelta)) (delta-fmap tailDelta ds)))
  ≡⟨ cong (\de -> delta x (delta-mu de)) (functor-law-2 delta-mu (delta-fmap tailDelta) (delta-fmap tailDelta ds)) ⟩
  delta x (delta-mu (delta-fmap (delta-mu {n = n}) (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta ds))))
  ≡⟨ cong (\de -> delta x de) (monad-law-1 (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta ds)))  ⟩
  delta x (delta-mu (delta-mu (delta-fmap (delta-fmap tailDelta) (delta-fmap tailDelta ds))))
  ≡⟨ cong (\de -> delta x (delta-mu de)) (delta-mu-is-nt tailDelta (delta-fmap tailDelta ds)) ⟩
  delta x (delta-mu (delta-fmap tailDelta (delta-mu (delta-fmap tailDelta ds)))) ≡⟨ refl ⟩
  delta (headDelta (delta x d)) (delta-mu (delta-fmap tailDelta (delta-mu (delta-fmap tailDelta ds)))) ≡⟨ refl ⟩
  delta-mu (delta (delta x d) (delta-mu (delta-fmap tailDelta ds))) ≡⟨ refl ⟩
  delta-mu (delta (headDelta (delta (delta x d) dd)) (delta-mu (delta-fmap tailDelta ds))) ≡⟨ refl ⟩
  delta-mu (delta-mu (delta (delta (delta x d) dd) ds)) ≡⟨ refl ⟩
  (delta-mu ∙ delta-mu) (delta (delta (delta x d) dd) ds)
  ∎
{-
begin
  (delta-mu ∙ delta-fmap delta-mu) (delta d ds) ≡⟨ refl ⟩
  delta-mu (delta-fmap delta-mu (delta d ds)) ≡⟨ refl ⟩
  delta-mu (delta (delta-mu d) (delta-fmap delta-mu ds)) ≡⟨ refl ⟩
  delta (headDelta (delta-mu d)) (delta-mu (delta-fmap tailDelta (delta-fmap delta-mu ds))) ≡⟨ {!!} ⟩
  delta (headDelta (headDelta d)) (delta-mu (delta-fmap tailDelta (delta-mu (delta-fmap tailDelta ds)))) ≡⟨ refl ⟩
  delta-mu (delta (headDelta d) (delta-mu (delta-fmap tailDelta ds))) ≡⟨ refl ⟩
  delta-mu (delta-mu (delta d ds)) ≡⟨ refl ⟩
  (delta-mu ∙ delta-mu) (delta d ds)
  ∎
-}




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
  ≡⟨ cong (\de -> delta x (delta-mu de)) (sym (functor-law-2 tailDelta delta-eta d)) ⟩
  delta x (delta-mu (delta-fmap (tailDelta ∙ delta-eta {n = S n}) d))  ≡⟨ refl ⟩
  delta x (delta-mu (delta-fmap (delta-eta {n = n}) d))  ≡⟨ cong (\de -> delta x de) (delta-left-unity-law d) ⟩
  delta x d ≡⟨ refl ⟩
  id (delta x d)  ∎



delta-is-monad : {l : Level} {n : Nat} -> Monad {l} (\A -> Delta A (S n))  delta-is-functor


delta-is-monad = record { eta    = delta-eta;
                          mu     = delta-mu;
                          return = delta-eta;
                          bind   = delta-bind;
                          eta-is-nt = delta-eta-is-nt;
                          association-law = monad-law-1;
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
