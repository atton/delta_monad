open import list
open import basic

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module delta where


data Delta {l : Level} (A : Set l) : (Set (suc l)) where
  mono    : A -> Delta A
  delta   : A -> Delta A -> Delta A

deltaAppend : {l : Level} {A : Set l} -> Delta A -> Delta A -> Delta A
deltaAppend (mono x) d     = delta x d
deltaAppend (delta x d) ds = delta x (deltaAppend d ds)

headDelta : {l : Level} {A : Set l} -> Delta A -> Delta A
headDelta (mono x)    = mono x
headDelta (delta x _) = mono x

tailDelta : {l : Level} {A : Set l} -> Delta A -> Delta A
tailDelta (mono x)     = mono x
tailDelta (delta  _ d) = d


-- Functor
fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> (Delta A) -> (Delta B)
fmap f (mono x)    = mono (f x)
fmap f (delta x d) = delta (f x) (fmap f d)



-- Monad (Category)
eta : {l : Level} {A : Set l} -> A -> Delta A
eta x = mono x

bind : {l ll : Level} {A : Set l} {B : Set ll} -> (Delta A) -> (A -> Delta B) -> Delta B
bind (mono x)    f = f x
bind (delta x d) f = deltaAppend (headDelta (f x)) (bind d (tailDelta ∙ f))

-- can not apply id. because different Level
mu : {l : Level} {A : Set l} -> Delta (Delta A) -> Delta A
mu d = bind d id 


returnS : {l : Level} {A : Set l} -> A -> Delta A
returnS x = mono x

returnSS : {l : Level} {A : Set l} -> A -> A -> Delta A
returnSS x y = deltaAppend (returnS x) (returnS y)


-- Monad (Haskell)
return : {l : Level} {A : Set l} -> A -> Delta A
return = eta

_>>=_ : {l ll : Level} {A : Set l} {B : Set ll} ->
        (x : Delta A) -> (f : A -> (Delta B)) -> (Delta B)
(mono x) >>= f    = f x
(delta x d) >>= f = deltaAppend (headDelta (f x)) (d >>= (tailDelta ∙ f))



-- proofs


-- Functor-laws

-- Functor-law-1 : T(id) = id'
functor-law-1 :  {l : Level} {A : Set l} ->  (d : Delta A) -> (fmap id) d ≡ id d
functor-law-1 (mono x)    = refl
functor-law-1 (delta x d) = cong (delta x) (functor-law-1 d)

-- Functor-law-2 : T(f . g) = T(f) . T(g)
functor-law-2 : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                (f : B -> C) -> (g : A -> B) -> (d : Delta A) ->
                (fmap (f ∙ g)) d ≡ ((fmap f) ∙ (fmap g)) d
functor-law-2 f g (mono x)    = refl
functor-law-2 f g (delta x d) = cong (delta (f (g x))) (functor-law-2 f g d)



-- Monad-laws (Category)

-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) d) ≡ ((mu ∙ mu) d)
monad-law-1 (mono d)    = refl
monad-law-1 (delta (mono (mono x)) (mono (mono (mono x₁)))) = refl
monad-law-1 (delta (mono (delta x x₁)) (mono (mono (mono x₂)))) = refl
monad-law-1 (delta (delta (mono x) (mono x₁)) (mono (mono (mono x₂)))) = refl
monad-law-1 (delta (delta (delta x x₁) (mono x₂)) (mono (mono (mono x₃)))) = refl
monad-law-1 (delta (delta (mono x) (delta (mono x₁) x₂)) (mono (mono (mono x₃)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (mono x₂) x₃)) (mono (mono (mono x₄)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (mono (mono x₃)))) (mono (mono (mono x₄)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (mono x₃)) (mono (mono x₄)))) (mono (mono (mono x₅)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (mono x₃))) (mono (mono x₄)))) (mono (mono (mono x₅)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (mono x₄))) (mono (mono x₅)))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (mono x₄)))) (mono (mono x₅)))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (mono (mono x₆)))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (mono x₅))))) (mono (mono x₆)))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (mono (mono x₇)))) (mono (mono (mono x₈)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ x₆))))) (mono (mono x₇)))) (mono (mono (mono x₈)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ x₇))))) (mono (mono x₈)))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (mono (delta x₃ (mono x₄))))) (mono (mono (mono x₅)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (mono x₃)) (mono (delta x₄ (mono x₅))))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ x₃)) (mono (delta x₄ (mono x₅))))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ x₄)) (mono (delta x₅ (mono x₆))))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (mono (delta x₃ (delta x₄ (mono x₅)))))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (mono x₃)) (mono (delta x₄ (delta x₅ (mono x₆)))))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (mono x₃))) (mono (delta x₄ (delta x₅ (mono x₆)))))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (delta x (mono x₁)) (delta (delta x₂ (delta x₃ (mono x₄))) (mono (delta x₅ (delta x₆ (mono x₇)))))) (mono (mono (mono x₈)))) = refl
monad-law-1 (delta (delta (delta x (delta x₁ x₂)) (delta (delta x₃ (delta x₄ (mono x₅))) (mono (delta x₆ (delta x₇ (mono x₈)))))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (mono x₄)))) (mono (delta x₅ (delta x₆ (mono x₇)))))) (mono (mono (mono x₈)))) = refl
monad-law-1 (delta (delta (delta x (mono x₁)) (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (mono (delta x₆ (delta x₇ (mono x₈)))))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (delta x (delta x₁ x₂)) (delta (delta x₃ (delta x₄ (delta x₅ (mono x₆)))) (mono (delta x₇ (delta x₈ (mono x₉)))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (mono x₅))))) (mono (delta x₆ (delta x₇ (mono x₈)))))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (delta x (mono x₁)) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (mono (delta x₇ (delta x₈ (mono x₉)))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (delta x (delta x₁ x₂)) (delta (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇))))) (mono (delta x₈ (delta x₉ (mono x₁₀)))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆)))))) (mono (delta x₇ (delta x₈ (mono x₉)))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (mono (delta x₈ (delta x₉ (mono x₁₀)))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇))))))) (mono (delta x₈ (delta x₉ (mono x₁₀)))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (mono (delta x₉ (delta x₁₀ (mono x₁₁)))))) (mono (mono (mono x₁₂)))) = refl
-- x (Delta A)... x7
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ x₈))))))) (mono (delta x₉ (delta x₁₀ (mono x₁₁)))))) (mono (mono (mono x₁₂)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ x₉))))))) (mono (delta x₁₀ (delta x₁₁ (mono x₁₂)))))) (mono (mono (mono x₁₃)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (mono (delta x₃ (delta x₄ (delta x₅ (mono x₆))))))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (mono x₃)) (mono (delta x₄ (delta x₅ (delta x₆ (mono x₇))))))) (mono (mono (mono x₈)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (mono x₃))) (mono (delta x₄ (delta x₅ (delta x₆ (mono x₇))))))) (mono (mono (mono x₈)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (mono x₄))) (mono (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (mono x₄)))) (mono (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (mono (delta x₆ (delta x₇ (delta x₈ (mono x₉))))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (mono x₅))))) (mono (delta x₆ (delta x₇ (delta x₈ (mono x₉))))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (mono (delta x₇ (delta x₈ (delta x₉ (mono x₁₀))))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆)))))) (mono (delta x₇ (delta x₈ (delta x₉ (mono x₁₀))))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (mono (delta x₈ (delta x₉ (delta x₁₀ (mono x₁₁))))))) (mono (mono (mono x₁₂)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇))))))) (mono (delta x₈ (delta x₉ (delta x₁₀ (mono x₁₁))))))) (mono (mono (mono x₁₂)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (mono (delta x₉ (delta x₁₀ (delta x₁₁ (mono x₁₂))))))) (mono (mono (mono x₁₃)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ x₈))))))) (mono (delta x₉ (delta x₁₀ (delta x₁₁ (mono x₁₂))))))) (mono (mono (mono x₁₃)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ x₉))))))) (mono (delta x₁₀ (delta x₁₁ (delta x₁₂ (mono x₁₃))))))) (mono (mono (mono x₁₄)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (mono (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))))) (mono (mono (mono x₈)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (mono x₃)) (mono (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈)))))))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (mono x₃))) (mono (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈)))))))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (mono x₄))) (mono (delta x₅ (delta x₆ (delta x₇ (delta x₈ (mono x₉)))))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (mono x₄)))) (mono (delta x₅ (delta x₆ (delta x₇ (delta x₈ (mono x₉)))))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (mono (delta x₆ (delta x₇ (delta x₈ (delta x₉ (mono x₁₀)))))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (mono x₅))))) (mono (delta x₆ (delta x₇ (delta x₈ (delta x₉ (mono x₁₀)))))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (mono (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (mono x₁₁)))))))) (mono (mono (mono x₁₂)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆)))))) (mono (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (mono x₁₁)))))))) (mono (mono (mono x₁₂)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (mono (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (mono x₁₂)))))))) (mono (mono (mono x₁₃)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇))))))) (mono (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (mono x₁₂)))))))) (mono (mono (mono x₁₃)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (mono (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (mono x₁₃)))))))) (mono (mono (mono x₁₄)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ x₈))))))) (mono (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (mono x₁₃)))))))) (mono (mono (mono x₁₄)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ x₉))))))) (mono (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (mono x₁₄)))))))) (mono (mono (mono x₁₅)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (mono (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ x₈)))))))) (mono (mono (mono x₉)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (mono x₃)) (mono (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ x₉)))))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (mono x₃))) (mono (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ x₉)))))))) (mono (mono (mono x₁₀)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (mono x₄))) (mono (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ x₁₀)))))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (mono x₄)))) (mono (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ x₁₀)))))))) (mono (mono (mono x₁₁)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (mono (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ x₁₁)))))))) (mono (mono (mono x₁₂)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (mono x₅))))) (mono (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ x₁₁)))))))) (mono (mono (mono x₁₂)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (mono (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ x₁₂)))))))) (mono (mono (mono x₁₃)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆)))))) (mono (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ x₁₂)))))))) (mono (mono (mono x₁₃)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (mono (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ x₁₃)))))))) (mono (mono (mono x₁₄)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇))))))) (mono (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ x₁₃)))))))) (mono (mono (mono x₁₄)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (mono (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ x₁₄)))))))) (mono (mono (mono x₁₅)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ x₈))))))) (mono (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ x₁₄)))))))) (mono (mono (mono x₁₅)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ x₉))))))) (mono (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ x₁₅)))))))) (mono (mono (mono x₁₆)))) = refl
-- 0, 2
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (delta (mono x₃) (mono (mono x₄))))) (mono (mono (mono x₅)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (delta (mono x₃) (mono (delta x₄ (mono x₅)))))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (delta (mono x₃) (mono (delta x₄ (delta x₅ x₆)))))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (delta (mono x₃) (delta x₄ (mono x₅))))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (delta (mono x₃) (delta x₄ (delta x₅ x₆))))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (delta (delta x₃ x₄) (mono x₅)))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (mono x₂)) (delta (delta x₃ x₄) (delta x₅ x₆)))) (mono (mono (mono x₇)))) = refl
monad-law-1 (delta (delta (mono x) (delta (delta x₁ (delta x₂ x₃)) (delta x₄ x₅))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta (delta x₂ x₃) (delta x₄ x₅))) (mono (mono (mono x₆)))) = refl
monad-law-1 (delta (mono x) (mono (mono (delta x₁ d)))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (mono (mono (delta x₂ (mono x₃))))) = refl
monad-law-1 (delta (delta (delta x x₁) (mono (mono x₂))) (mono (mono (delta x₃ (mono x₄))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (mono (mono (delta x₃ (mono x₄))))) = refl
monad-law-1 (delta (delta (delta x x₁) (mono (delta x₂ (mono x₃)))) (mono (mono (delta x₄ (mono x₅))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ x₃)))) (mono (mono (delta x₄ (mono x₅))))) = refl
monad-law-1 (delta (delta (delta x x₁) (mono (delta x₂ (delta x₃ x₄)))) (mono (mono (delta x₅ (mono x₆))))) = refl
monad-law-1 (delta (delta (mono x) (mono x₁)) (mono (mono (delta x₂ (delta x₃ d))))) = refl
monad-law-1 (delta (delta (delta x x₁) (mono x₂)) (mono (mono (delta x₃ (delta x₄ d))))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ (mono x₂))) (mono (mono (delta x₃ d)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta x₂ (mono x₃))) (mono (mono (delta x₄ d)))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ (delta x₂ x₃))) (mono (mono (delta x₄ d)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta x₂ (delta x₃ x₄))) (mono (mono (delta x₅ d)))) = refl
monad-law-1 (delta (mono (mono x)) (mono (delta (mono x₁) d₁))) = refl
monad-law-1 (delta (mono (mono x)) (mono (delta (delta x₁ d) d₁))) = refl
monad-law-1 (delta (mono (delta x (mono x₁))) (mono (delta (mono x₂) (mono d₁)))) = refl
monad-law-1 (delta (mono (delta x (mono x₁))) (mono (delta (delta x₂ d) (mono d₁)))) = refl
monad-law-1 (delta (mono (delta x (delta x₁ x₂))) (mono (delta (mono x₃) (mono d₁)))) = refl
monad-law-1 (delta (mono (delta x (delta x₁ x₂))) (mono (delta (delta x₃ d) (mono d₁)))) = refl
monad-law-1 (delta (mono (delta x x₁)) (mono (delta (mono x₂) (delta d₁ (mono d₂))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (mono (delta (delta x₂ d) (delta d₁ (mono d₂))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (mono (delta (mono x₂) (delta d₁ (delta d₂ (mono d₃)))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (mono (delta (delta x₂ d) (delta d₁ (delta d₂ (mono d₃)))))) = refl
monad-law-1 (delta (mono (delta x (mono x₁))) (mono (delta (mono x₂) (delta d₁ (delta d₂ (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x (mono x₁))) (mono (delta (delta x₂ d) (delta d₁ (delta d₂ (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x (delta x₁ (mono x₂)))) (mono (delta (mono x₃) (delta d₁ (delta d₂ (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x (delta x₁ (mono x₂)))) (mono (delta (delta x₃ d) (delta d₁ (delta d₂ (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x (delta x₁ (delta x₂ (mono x₃))))) (mono (delta (mono x₄) (delta d₁ (delta d₂ (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x (delta x₁ (delta x₂ (mono x₃))))) (mono (delta (delta x₄ d) (delta d₁ (delta d₂ (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x (delta x₁ (delta x₂ (delta x₃ x₄))))) (mono (delta (mono x₅) (delta d₁ (delta d₂ (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x (delta x₁ (delta x₂ (delta x₃ x₄))))) (mono (delta (delta x₅ d) (delta d₁ (delta d₂ (delta d₃ d₄)))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (mono (delta (mono x₂) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (mono (delta (delta x₂ d) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (mono (delta (mono x₃) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (mono (delta (delta x₃ d) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (mono (delta (mono x₄) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (mono (delta (delta x₄ d) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (mono x₄)))))) (mono (delta (mono x₅) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (mono x₄)))))) (mono (delta (delta x₅ d) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ x₅)))))) (mono (delta (mono x₆) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ x₅)))))) (mono (delta (delta x₆ d) (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (mono (delta (mono x₂) (delta d₁ (mono d₂))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (mono (delta (delta x₂ d) (delta d₁ (mono d₂))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ x₂))) (mono (delta (mono x₃) (delta d₁ (mono d₂))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ x₂))) (mono (delta (delta x₃ d) (delta d₁ (mono d₂))))) = refl
monad-law-1 (delta (delta (mono x) (mono x₁)) (mono (delta (mono x₂) (delta d₁ (delta d₂ d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono x₁)) (mono (delta (delta x₂ d) (delta d₁ (delta d₂ d₃))))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ x₂)) (mono (delta (mono x₃) d₁))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ x₂)) (mono (delta (delta x₃ d) d₁))) = refl
monad-law-1 (delta (delta (delta x x₁) x₂) (mono (delta (mono x₃) d₁))) = refl
monad-law-1 (delta (delta (delta x x₁) x₂) (mono (delta (delta x₃ d) d₁))) = refl
--
monad-law-1 (delta (mono x) (delta (mono (mono x₁)) (mono (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (mono x₁)) (delta (mono (mono x₂)) (mono (mono d₁)))) = refl
monad-law-1 (delta (delta (delta x x₁) (mono x₂)) (delta (mono (mono x₃)) (mono (mono d₁)))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ x₂)) (delta (mono (mono x₃)) (mono (mono d₁)))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta x₂ x₃)) (delta (mono (mono x₄)) (mono (mono d₁)))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (mono x₂) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (mono x₂) (delta (mono x₃) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (mono x₂) (delta (delta x₃ (mono x₄)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (mono x₂) (delta (delta x₃ (delta x₄ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (mono x₃)) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (mono x₃)) (delta (mono x₄) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (mono x₃)) (delta (delta x₄ (mono x₅)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (mono x₃)) (delta (delta x₄ (delta x₅ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (mono x₄))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (mono x₄))) (delta (mono x₅) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (mono x₄))) (delta (delta x₅ (mono x₆)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (mono x₄))) (delta (delta x₅ (delta x₆ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (delta (mono x₆) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (delta (delta x₆ (mono x₇)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (mono x₅)))) (delta (delta x₆ (delta x₇ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (delta (mono x₇) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (delta (delta x₇ (mono x₈)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆))))) (delta (delta x₇ (delta x₈ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (mono x₈) (mono (mono x₉))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (delta x₈ (mono x₉)) (mono (mono x₁₀))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (delta x₈ (delta x₉ d₂)) (mono (mono x₁₀))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (mono x₈) (mono (delta x₉ d₃))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (delta x₈ (mono x₉)) (mono (delta x₁₀ (mono x₁₁)))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (delta x₈ (delta x₉ d₂)) (mono (delta x₁₀ (mono x₁₁)))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (delta x₈ (mono x₉)) (mono (delta x₁₀ (delta x₁₁ d₃)))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (delta x₈ (delta x₉ d₂)) (mono (delta x₁₀ (delta x₁₁ d₃)))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (mono x₈) (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (delta x₈ (mono x₉)) (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (mono x₇)))))) (delta (delta x₈ (delta x₉ d₂)) (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (mono x₉) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (mono x₁₀)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (delta x₁₀ d₂)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (mono x₁₀)) (delta d₃ (mono d₄))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (delta x₁₀ d₂)) (delta d₃ (mono d₄))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (mono x₁₀)) (delta (mono x₁₁) (delta (mono x₁₂) (mono (mono x₁₃))))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (delta x₁₀ d₂)) (delta (mono x₁₁) (delta (mono x₁₂) (mono (mono x₁₃))))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (mono x₁₀)) (delta (delta x₁₁ d₃) (delta (mono x₁₂) (mono (mono x₁₃))))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (delta x₁₀ d₂)) (delta (delta x₁₁ d₃) (delta (mono x₁₂) (mono (mono x₁₃))))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (mono x₁₀)) (delta d₃ (delta (delta x₁₁ d₄) (mono (mono x₁₂))))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (delta x₁₀ d₂)) (delta d₃ (delta (delta x₁₁ d₄) (mono (mono x₁₂))))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (mono x₁₀)) (delta d₃ (delta d₄ (mono (delta x₁₁ d₅))))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (delta x₁₀ d₂)) (delta d₃ (delta d₄ (mono (delta x₁₁ d₅))))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (mono x₁₀)) (delta d₃ (delta d₄ (delta d₅ d₆)))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (mono x₈))))))) (delta (delta x₉ (delta x₁₀ d₂)) (delta d₃ (delta d₄ (delta d₅ d₆)))))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (mono x₉)))))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (mono x₉)))))))) (delta (mono x₁₀) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (mono x₉)))))))) (delta (delta x₁₀ (mono x₁₁)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (mono x₉)))))))) (delta (delta x₁₀ (delta x₁₁ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (mono x₁₀))))))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (mono x₁₀))))))))) (delta (mono x₁₁) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (mono x₁₀))))))))) (delta (delta x₁₁ (mono x₁₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (mono x₁₀))))))))) (delta (delta x₁₁ (delta x₁₂ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (mono x₁₁)))))))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (mono x₁₁)))))))))) (delta (mono x₁₂) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (mono x₁₁)))))))))) (delta (delta x₁₂ (mono x₁₃)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (mono x₁₁)))))))))) (delta (delta x₁₂ (delta x₁₃ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (mono x₁₂))))))))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (mono x₁₂))))))))))) (delta (mono x₁₃) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (mono x₁₂))))))))))) (delta (delta x₁₃ (mono x₁₄)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (mono x₁₂))))))))))) (delta (delta x₁₃ (delta x₁₄ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (mono x₁₃)))))))))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (mono x₁₃)))))))))))) (delta (mono x₁₄) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (mono x₁₃)))))))))))) (delta (delta x₁₄ (mono x₁₅)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (mono x₁₃)))))))))))) (delta (delta x₁₄ (delta x₁₅ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (mono x₁₄))))))))))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (mono x₁₄))))))))))))) (delta (mono x₁₅) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (mono x₁₄))))))))))))) (delta (delta x₁₅ (mono x₁₆)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (mono x₁₄))))))))))))) (delta (delta x₁₅ (delta x₁₆ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ d₁))))))))))))) (mono d₂))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ d₁))))))))))))) (delta (mono x₁₅) d₃))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (mono x₁₅)))))))))))))) (delta (delta x₁₆ (mono x₁₇)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (mono x₁₅)))))))))))))) (delta (delta x₁₆ (delta x₁₇ d₂)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (delta x₁₅ (mono x₁₆))))))))))))))) (delta (delta x₁₇ (mono x₁₈)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (delta x₁₅ (mono x₁₆))))))))))))))) (delta (delta x₁₇ (delta x₁₈ d₂)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (delta x₁₅ (delta x₁₆ (mono x₁₇)))))))))))))))) (delta (delta x₁₈ (mono x₁₉)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (delta x₁₅ (delta x₁₆ (mono x₁₇)))))))))))))))) (delta (delta x₁₈ (delta x₁₉ d₂)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (delta x₁₅ (delta x₁₆ (delta x₁₇ d₁)))))))))))))))) (delta (delta x₁₈ (mono x₁₉)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (delta x₁₅ (delta x₁₆ (delta x₁₇ d₁)))))))))))))))) (delta (delta x₁₈ (delta x₁₉ d₂)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (mono x₁₅)))))))))))))) (delta (delta x₁₆ (mono x₁₇)) (delta (mono x₁₈) d₄)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (mono x₁₅)))))))))))))) (delta (delta x₁₆ (delta x₁₇ d₂)) (delta (mono x₁₈) d₄)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (mono x₁₅)))))))))))))) (delta (delta x₁₆ (mono x₁₇)) (delta (delta x₁₈ d₃) d₄)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (mono x₁₅)))))))))))))) (delta (delta x₁₆ (delta x₁₇ d₂)) (delta (delta x₁₈ d₃) d₄)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (delta x₁₅ d₁)))))))))))))) (delta (delta x₁₆ (mono x₁₇)) (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (mono x)) (delta (mono (mono x₁)) (mono (delta (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ (delta x₇ (delta x₈ (delta x₉ (delta x₁₀ (delta x₁₁ (delta x₁₂ (delta x₁₃ (delta x₁₄ (delta x₁₅ d₁)))))))))))))) (delta (delta x₁₆ (delta x₁₇ d₂)) (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (mono x₃) (mono d₂))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (mono x₃) (delta (mono x₄) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (mono x₃) (delta (delta x₄ (mono x₅)) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (mono x₃) (delta (delta x₄ (delta x₅ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ d₁) (mono d₂))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (delta (mono x₅) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (delta (delta x₅ (mono x₆)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (delta (delta x₅ (delta x₆ d₂)) (mono d₃)))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (delta (delta x₅ (mono x₆)) (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (delta (delta x₅ (delta x₆ d₂)) (delta d₃ d₄)))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (delta x₄ (mono x₅))) (delta (mono x₆) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (delta x₄ (mono x₅))) (delta (delta x₆ (mono x₇)) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (delta x₄ (mono x₅))) (delta (delta x₆ (delta x₇ d₂)) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (delta x₄ (delta x₅ d₁))) (delta (mono x₆) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (delta x₄ (delta x₅ d₁))) (delta (delta x₆ (mono x₇)) d₃))))) = refl
monad-law-1 (delta (mono (delta x x₁)) (delta (mono (mono x₂)) (mono (delta (delta x₃ (delta x₄ (delta x₅ d₁))) (delta (delta x₆ (delta x₇ d₂)) d₃))))) = refl
--
monad-law-1 (delta (delta (mono x) (mono x₁)) (delta (mono (mono x₂)) (mono (delta (mono x₃) (mono (mono x₄)))))) = refl
monad-law-1 (delta (delta (delta x x₁) (mono x₂)) (delta (mono (mono x₃)) (mono (delta (mono x₄) (mono (mono x₅)))))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ (mono x₂))) (delta (mono (mono x₃)) (mono (delta (mono x₄) (mono (mono x₅)))))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta x₂ (mono x₃))) (delta (mono (mono x₄)) (mono (delta (mono x₅) (mono (mono x₆)))))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ (delta x₂ x₃))) (delta (mono (mono x₄)) (mono (delta (mono x₅) (mono (mono x₆)))))) = refl
monad-law-1 (delta (delta (delta x x₁) (delta x₂ (delta x₃ x₄))) (delta (mono (mono x₅)) (mono (delta (mono x₆) (mono (mono x₇)))))) = refl
monad-law-1 (delta (delta (mono x) x₁) (delta (mono (mono x₂)) (mono (delta (mono x₃) (mono (delta x₄ d₂)))))) = refl
monad-law-1 (delta (delta (delta x x₁) x₂) (delta (mono (mono x₃)) (mono (delta (mono x₄) (mono (delta x₅ d₂)))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (delta (mono (mono x₂)) (mono (delta (mono x₃) (delta (mono x₄) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (delta (mono (mono x₂)) (mono (delta (mono x₃) (delta (delta x₄ (mono x₅)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (delta (mono (mono x₂)) (mono (delta (mono x₃) (delta (delta x₄ (delta x₅ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (mono x₅) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (delta x₅ (mono x₆)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (delta x₅ (delta x₆ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (delta (mono (mono x₄)) (mono (delta (mono x₅) (delta (mono x₆) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (delta (mono (mono x₄)) (mono (delta (mono x₅) (delta (delta x₆ (mono x₇)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (delta (mono (mono x₄)) (mono (delta (mono x₅) (delta (delta x₆ (delta x₇ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (mono x₄)))))) (delta (mono (mono x₅)) (mono (delta (mono x₆) (delta (mono x₇) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (mono x₄)))))) (delta (mono (mono x₅)) (mono (delta (mono x₆) (delta (delta x₇ (mono x₈)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (mono x₄)))))) (delta (mono (mono x₅)) (mono (delta (mono x₆) (delta (delta x₇ (delta x₈ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (mono x₅))))))) (delta (mono (mono x₆)) (mono (delta (mono x₇) (delta (mono x₈) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (mono x₅))))))) (delta (mono (mono x₆)) (mono (delta (mono x₇) (delta (delta x₈ (mono x₉)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (mono x₅))))))) (delta (mono (mono x₆)) (mono (delta (mono x₇) (delta (delta x₈ (delta x₉ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆)))))))) (delta (mono (mono x₇)) (mono (delta (mono x₈) (delta (mono x₉) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆)))))))) (delta (mono (mono x₇)) (mono (delta (mono x₈) (delta (delta x₉ (mono x₁₀)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (mono x₆)))))))) (delta (mono (mono x₇)) (mono (delta (mono x₈) (delta (delta x₉ (delta x₁₀ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ x₇)))))))) (delta (mono (mono x₈)) (mono (delta (mono x₉) (delta (mono x₁₀) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ x₇)))))))) (delta (mono (mono x₈)) (mono (delta (mono x₉) (delta (delta x₁₀ (mono x₁₁)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ (delta x₅ (delta x₆ x₇)))))))) (delta (mono (mono x₈)) (mono (delta (mono x₉) (delta (delta x₁₀ (delta x₁₁ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ x₂)) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (mono x₅) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ x₂)) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (delta x₅ (mono x₆)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (delta x₁ x₂)) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (delta x₅ (delta x₆ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (delta x x₁) x₂) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (mono x₅) d₃))))) = refl
monad-law-1 (delta (delta (delta x x₁) x₂) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (delta x₅ (mono x₆)) d₃))))) = refl
monad-law-1 (delta (delta (delta x x₁) x₂) (delta (mono (mono x₃)) (mono (delta (mono x₄) (delta (delta x₅ (delta x₆ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (mono d₂))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (delta (mono x₅) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (delta (delta x₅ (mono x₆)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (mono x₁))) (delta (mono (mono x₂)) (mono (delta (delta x₃ (mono x₄)) (delta (delta x₅ (delta x₆ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (delta (mono (mono x₃)) (mono (delta (delta x₄ (mono x₅)) (mono d₂))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (delta (mono (mono x₃)) (mono (delta (delta x₄ (mono x₅)) (delta (mono x₆) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (delta (mono (mono x₃)) (mono (delta (delta x₄ (mono x₅)) (delta (delta x₆ (mono x₇)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (mono x₂)))) (delta (mono (mono x₃)) (mono (delta (delta x₄ (mono x₅)) (delta (delta x₆ (delta x₇ d₂)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (delta (mono (mono x₄)) (mono (delta (delta x₅ (mono x₆)) (mono d₂))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (delta (mono (mono x₄)) (mono (delta (delta x₅ (mono x₆)) (delta (mono x₇) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (delta (mono (mono x₄)) (mono (delta (delta x₅ (mono x₆)) (delta (delta x₇ (mono x₈)) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (delta (mono (mono x₄)) (mono (delta (delta x₅ (mono x₆)) (delta (delta x₇ (delta x₈ (mono x₉))) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (mono x₃))))) (delta (mono (mono x₄)) (mono (delta (delta x₅ (mono x₆)) (delta (delta x₇ (delta x₈ (delta x₉ d₂))) d₃))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (mono x₄)))))) (delta (mono (mono x₅)) (mono (delta (delta x₆ (mono x₇)) (mono d₂))))) = refl
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (mono x₄)))))) (delta (mono (mono x₅)) (mono (delta (delta x₆ (mono x₇)) (delta d₂ d₃))))) = {!!}
monad-law-1 (delta (delta (mono x) (mono (delta x₁ (delta x₂ (delta x₃ (delta x₄ x₅)))))) (delta (mono (mono x₆)) (mono (delta (delta x₇ (mono x₈)) d₂)))) = {!!}
monad-law-1 (delta (delta (mono x) (delta x₁ x₂)) (delta (mono (mono x₃)) (mono (delta (delta x₄ (mono x₅)) d₂)))) = {!!}
monad-law-1 (delta (delta (delta x x₁) x₂) (delta (mono (mono x₃)) (mono (delta (delta x₄ (mono x₅)) d₂)))) = {!!}
monad-law-1 (delta (delta x x₁) (delta (mono (mono x₂)) (mono (delta (delta x₃ (delta x₄ d₁)) d₂)))) = {!!}
--
monad-law-1 (delta x (delta (mono (mono x₁)) (delta d₁ d₂))) = {!!}
monad-law-1 (delta x (delta (mono (delta x₁ d)) d₁)) = {!!}
monad-law-1 (delta x (delta (delta d d₁) d₂)) = {!!}



{-
-- monad-law-2-2 :  join . return = id
monad-law-2-2 : {l : Level} {A : Set l } -> (s : Delta A) -> (mu ∙ eta) s ≡ id s
monad-law-2-2 (similar lx x ly y) = refl

-- monad-law-3 : return . f = fmap f . return
monad-law-3 : {l : Level} {A B : Set l} (f : A -> B) (x : A) -> (eta ∙ f) x ≡ (fmap f ∙ eta) x
monad-law-3 f x = refl

-- monad-law-4 : join . fmap (fmap f) = fmap f . join
monad-law-4 : {l ll : Level} {A : Set l} {B : Set ll} (f : A -> B) (s : Delta (Delta A)) ->
              (mu ∙ fmap (fmap f)) s ≡ (fmap f ∙ mu) s
monad-law-4 f (similar lx (similar llx x _ _) ly (similar _ _ lly y)) = refl


-- Monad-laws (Haskell)
-- monad-law-h-1 : return a >>= k  =  k a
monad-law-h-1 : {l ll : Level} {A : Set l} {B : Set ll} ->
                (a : A) -> (k : A -> (Delta B)) ->
                (return a >>= k)  ≡ (k a)
monad-law-h-1 a k = refl



-- monad-law-h-2 : m >>= return  =  m
monad-law-h-2 : {l : Level}{A : Set l} -> (m : Delta A) -> (m >>= return)  ≡ m
monad-law-h-2 (mono x)    = refl
monad-law-h-2 (delta x d) = cong (delta x) (monad-law-h-2 d)




-- monad-law-h-3 : m >>= (\x -> k x >>= h)  =  (m >>= k) >>= h
monad-law-h-3 : {l ll lll : Level} {A : Set l} {B : Set ll} {C : Set lll} ->
                (m : Delta A)  -> (k : A -> (Delta B)) -> (h : B -> (Delta C)) ->
                (m >>= (\x -> k x >>= h)) ≡ ((m >>= k) >>= h)
monad-law-h-3 (mono x) k h    = refl
monad-law-h-3 (delta x d) k h = begin
  (delta x d) >>= (\x -> k x >>= h)
  ≡⟨ refl ⟩
-- (delta x d) >>= f = deltaAppend (headDelta (f x)) (d >>= (tailDelta ∙ f))
  deltaAppend (headDelta ((\x -> k x >>= h) x)) (d >>= (tailDelta ∙ (\x -> k x >>= h)))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (k x >>= h)) (d >>= (tailDelta ∙ (\x -> k x >>= h)))
  ≡⟨ {!!} ⟩
  ((delta x d) >>= k) >>= h
  ∎
-}