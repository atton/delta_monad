open import list
open import basic
open import nat

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

headDelta : {l : Level} {A : Set l} -> Delta A -> A
headDelta (mono x)    = x
headDelta (delta x _) = x

tailDelta : {l : Level} {A : Set l} -> Delta A -> Delta A
tailDelta (mono x)    = mono x
tailDelta (delta _ d) = d

n-tail : {l : Level} {A : Set l} -> Nat -> ((Delta A) -> (Delta A))
n-tail O = id
n-tail (S n) =  tailDelta ∙ (n-tail n)


-- Functor
fmap : {l ll : Level} {A : Set l} {B : Set ll} -> (A -> B) -> (Delta A) -> (Delta B)
fmap f (mono x)    = mono  (f x)
fmap f (delta x d) = delta (f x) (fmap f d)



-- Monad (Category)
eta : {l : Level} {A : Set l} -> A -> Delta A
eta x = mono x

bind : {l ll : Level} {A : Set l} {B : Set ll} -> (Delta A) -> (A -> Delta B) -> Delta B
bind (mono x)    f = f x
bind (delta x d) f = delta (headDelta (f x)) (bind d (tailDelta ∙ f))

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
(delta x d) >>= f = delta (headDelta (f x)) (d >>= (tailDelta ∙ f))



-- proofs

-- sub-proofs

n-tail-plus : {l : Level} {A : Set l} -> (n : Nat) -> ((n-tail {l} {A} n) ∙ tailDelta) ≡ n-tail (S n)
n-tail-plus O     = refl
n-tail-plus (S n) = begin
  n-tail (S n) ∙ tailDelta             ≡⟨ refl ⟩
  (tailDelta ∙ (n-tail n)) ∙ tailDelta ≡⟨ refl ⟩
  tailDelta ∙ ((n-tail n) ∙ tailDelta) ≡⟨ cong (\t -> tailDelta ∙ t) (n-tail-plus n) ⟩
  n-tail (S (S n))
  ∎

n-tail-add : {l : Level} {A : Set l} {d : Delta A} -> (n m : Nat) -> (n-tail {l} {A} n) ∙ (n-tail m) ≡ n-tail (n + m)
n-tail-add O m = refl
n-tail-add (S n) O = begin
  n-tail (S n) ∙ n-tail O  ≡⟨ refl ⟩
  n-tail (S n)             ≡⟨ cong (\n -> n-tail n) (nat-add-right-zero (S n))⟩
  n-tail (S n + O)
  ∎
n-tail-add {l} {A} {d} (S n) (S m) =      begin
  n-tail (S n) ∙ n-tail (S m)             ≡⟨ refl ⟩
  (tailDelta ∙ (n-tail n)) ∙ n-tail (S m) ≡⟨ refl ⟩
  tailDelta ∙ ((n-tail n) ∙ n-tail (S m)) ≡⟨ cong (\t -> tailDelta ∙ t) (n-tail-add {l} {A} {d} n (S m)) ⟩
  tailDelta ∙ (n-tail (n + (S m)))        ≡⟨ refl ⟩
  n-tail (S (n + S m))                    ≡⟨ refl ⟩
  n-tail (S n + S m)                      ∎

tail-delta-to-mono : {l : Level} {A : Set l} -> (n : Nat) -> (x : A) ->
  (n-tail n) (mono x) ≡ (mono x)
tail-delta-to-mono O x     = refl
tail-delta-to-mono (S n) x =      begin
  n-tail (S n) (mono x)           ≡⟨ refl ⟩
  tailDelta (n-tail n (mono x))   ≡⟨ refl ⟩
  tailDelta (n-tail n (mono x))   ≡⟨ cong (\t -> tailDelta t) (tail-delta-to-mono n x) ⟩
  tailDelta (mono x)              ≡⟨ refl ⟩
  mono x                          ∎

head-delta-natural-transformation : {l ll : Level} {A : Set l} {B : Set ll} 
  -> (f : A -> B) -> (d : Delta A) -> headDelta (fmap f d) ≡ f (headDelta d)
head-delta-natural-transformation f (mono x)    = refl
head-delta-natural-transformation f (delta x d) = refl 

n-tail-natural-transformation  : {l ll : Level} {A : Set l} {B : Set ll}
  -> (n : Nat) -> (f : A -> B) -> (d : Delta A) ->  n-tail n (fmap f d) ≡ fmap f (n-tail n d)
n-tail-natural-transformation O f d            = refl
n-tail-natural-transformation (S n) f (mono x) = begin
  n-tail (S n) (fmap f (mono x))  ≡⟨ refl ⟩
  n-tail (S n) (mono (f x))       ≡⟨ tail-delta-to-mono (S n) (f x) ⟩
  (mono (f x))                    ≡⟨ refl ⟩
  fmap f (mono x)                 ≡⟨ cong (\d -> fmap f d) (sym (tail-delta-to-mono (S n) x)) ⟩
  fmap f (n-tail (S n) (mono x))  ∎
n-tail-natural-transformation (S n) f (delta x d) = begin
  n-tail (S n) (fmap f (delta x d))                 ≡⟨ refl ⟩
  n-tail (S n) (delta (f x) (fmap f d))             ≡⟨ cong (\t -> t (delta (f x) (fmap f d))) (sym (n-tail-plus n)) ⟩
  ((n-tail n) ∙ tailDelta) (delta (f x) (fmap f d)) ≡⟨ refl ⟩
  n-tail n (fmap f d)                               ≡⟨ n-tail-natural-transformation n f d ⟩
  fmap f (n-tail n d)                               ≡⟨ refl ⟩
  fmap f (((n-tail n) ∙ tailDelta) (delta x d))     ≡⟨ cong (\t -> fmap f (t (delta x d))) (n-tail-plus n) ⟩
  fmap f (n-tail (S n) (delta x d))                 ∎




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
{-

monad-law-1-5 : {l : Level} {A : Set l} -> (m : Nat) (n : Nat) -> (ds : Delta (Delta A)) ->
  n-tail n (bind ds (n-tail m))  ≡ bind (n-tail n ds) (n-tail (m + n))
monad-law-1-5 O O ds = refl
monad-law-1-5 O (S n) (mono ds) = begin
  n-tail (S n) (bind (mono ds) (n-tail O)) ≡⟨ refl ⟩
  n-tail (S n) ds ≡⟨ refl ⟩
  bind (mono ds) (n-tail (S n)) ≡⟨ cong (\de -> bind de (n-tail (S n))) (sym (tail-delta-to-mono (S n) ds)) ⟩
  bind (n-tail (S n) (mono ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (n-tail (S n) (mono ds)) (n-tail (O + S n))
  ∎
monad-law-1-5 O (S n) (delta d ds) = begin
  n-tail (S n) (bind (delta d ds) (n-tail O)) ≡⟨ refl ⟩
  n-tail (S n) (delta (headDelta d) (bind ds tailDelta )) ≡⟨ cong (\t -> t  (delta (headDelta d) (bind ds tailDelta ))) (sym (n-tail-plus n)) ⟩
  ((n-tail n) ∙ tailDelta) (delta (headDelta d) (bind ds tailDelta )) ≡⟨ refl ⟩
  (n-tail n) (bind ds tailDelta) ≡⟨ monad-law-1-5 (S O) n ds ⟩
  bind (n-tail n ds) (n-tail  (S n)) ≡⟨ refl ⟩
  bind (((n-tail n) ∙ tailDelta) (delta d ds)) (n-tail  (S n)) ≡⟨ cong (\t -> bind (t (delta d ds)) (n-tail  (S n))) (n-tail-plus n) ⟩
  bind (n-tail (S n) (delta d ds)) (n-tail  (S n)) ≡⟨ refl ⟩
  bind (n-tail (S n) (delta d ds)) (n-tail (O + S n))
  ∎
monad-law-1-5 (S m) n (mono (mono x)) = begin
  n-tail n (bind (mono (mono x)) (n-tail (S m))) ≡⟨ refl ⟩
  n-tail n (n-tail (S m) (mono x)) ≡⟨ cong (\de -> n-tail n de) (tail-delta-to-mono (S m) x)⟩
  n-tail n (mono x) ≡⟨ tail-delta-to-mono n x ⟩
  mono x  ≡⟨ sym (tail-delta-to-mono (S m + n) x) ⟩
  (n-tail (S m + n)) (mono x) ≡⟨ refl ⟩
  bind (mono (mono x)) (n-tail (S m + n)) ≡⟨ cong (\de -> bind de (n-tail (S m + n))) (sym (tail-delta-to-mono n (mono x))) ⟩
  bind (n-tail n (mono (mono x))) (n-tail (S m + n))
  ∎
monad-law-1-5 (S m) n (mono (delta x ds)) = begin
  n-tail n (bind (mono (delta x ds)) (n-tail (S m))) ≡⟨ refl ⟩
  n-tail n (n-tail (S m) (delta x ds)) ≡⟨ cong (\t -> n-tail n (t (delta x ds))) (sym (n-tail-plus m)) ⟩
  n-tail n (((n-tail m) ∙ tailDelta) (delta x ds)) ≡⟨ refl ⟩
  n-tail n ((n-tail m) ds) ≡⟨ cong (\t -> t ds) (n-tail-add {d = ds} n m)  ⟩
  n-tail (n + m) ds  ≡⟨ cong (\n -> n-tail n ds) (nat-add-sym n m) ⟩
  n-tail (m + n) ds  ≡⟨ refl ⟩
  ((n-tail (m + n)) ∙ tailDelta) (delta x ds)  ≡⟨ cong (\t -> t (delta x ds)) (n-tail-plus (m + n))⟩
  n-tail (S (m + n)) (delta x ds)  ≡⟨ refl ⟩
  n-tail (S m + n) (delta x ds)  ≡⟨ refl ⟩
  bind (mono (delta x ds)) (n-tail (S m + n)) ≡⟨ cong (\de -> bind de (n-tail (S m + n))) (sym (tail-delta-to-mono n (delta x ds))) ⟩
  bind (n-tail n (mono (delta x ds))) (n-tail (S m + n))
  ∎
monad-law-1-5 (S m) O (delta d ds) = begin
  n-tail O (bind (delta d ds) (n-tail (S m))) ≡⟨ refl ⟩
  (bind (delta d ds) (n-tail (S m))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S m)) d)) (bind ds (tailDelta ∙ (n-tail (S m)))) ≡⟨ refl ⟩
  bind (delta d ds) (n-tail (S m)) ≡⟨ refl ⟩
  bind (n-tail O (delta d ds)) (n-tail (S m)) ≡⟨ cong (\n -> bind (n-tail O (delta d ds)) (n-tail n)) (nat-add-right-zero (S m)) ⟩
  bind (n-tail O (delta d ds)) (n-tail (S m + O))
  ∎
monad-law-1-5 (S m) (S n) (delta d ds) = begin
  n-tail (S n) (bind (delta d ds) (n-tail (S m))) ≡⟨ cong (\t -> t ((bind (delta d ds) (n-tail (S m))))) (sym (n-tail-plus n)) ⟩
  ((n-tail n) ∙ tailDelta) (bind (delta d ds) (n-tail (S m))) ≡⟨ refl ⟩
  ((n-tail n) ∙ tailDelta) (delta (headDelta ((n-tail (S m)) d)) (bind ds (tailDelta ∙  (n-tail (S m))))) ≡⟨ refl ⟩
  (n-tail n) (bind ds (tailDelta ∙ (n-tail (S m)))) ≡⟨ refl ⟩
  (n-tail n) (bind ds (n-tail (S (S m)))) ≡⟨ monad-law-1-5 (S (S m)) n ds ⟩
  bind ((n-tail n) ds) (n-tail (S (S (m + n)))) ≡⟨ cong (\nm -> bind ((n-tail n) ds) (n-tail nm))  (sym (nat-right-increment (S m) n)) ⟩
  bind ((n-tail n) ds) (n-tail (S m + S n)) ≡⟨ refl ⟩
  bind (((n-tail n) ∙ tailDelta) (delta d ds)) (n-tail (S m + S n)) ≡⟨ cong (\t -> bind (t (delta d ds)) (n-tail (S m + S n))) (n-tail-plus n) ⟩
  bind (n-tail (S n) (delta d ds)) (n-tail (S m + S n))
  ∎

monad-law-1-4 : {l : Level} {A : Set l} -> (m n : Nat) -> (dd : Delta (Delta A)) ->
  headDelta ((n-tail n) (bind dd (n-tail m))) ≡ headDelta ((n-tail (m + n)) (headDelta (n-tail n dd)))
monad-law-1-4 O O (mono dd) = refl
monad-law-1-4 O O (delta dd dd₁) = refl
monad-law-1-4 O (S n) (mono dd) = begin
  headDelta (n-tail (S n) (bind (mono dd) (n-tail O))) ≡⟨ refl ⟩
  headDelta (n-tail (S n) dd)  ≡⟨ refl ⟩
  headDelta (n-tail (S n) (headDelta (mono dd))) ≡⟨ cong (\de -> headDelta (n-tail (S n) (headDelta de))) (sym (tail-delta-to-mono (S n) dd)) ⟩
  headDelta (n-tail (S n) (headDelta (n-tail (S n) (mono dd)))) ≡⟨ refl ⟩
  headDelta (n-tail (O + S n) (headDelta (n-tail (S n) (mono dd))))
  ∎
monad-law-1-4 O (S n) (delta d ds) = begin
  headDelta (n-tail (S n) (bind (delta d ds) (n-tail O))) ≡⟨ refl ⟩
  headDelta (n-tail (S n) (bind (delta d ds) id)) ≡⟨ refl ⟩
  headDelta (n-tail (S n) (delta (headDelta d) (bind ds tailDelta))) ≡⟨ cong (\t -> headDelta (t (delta (headDelta d) (bind ds tailDelta)))) (sym (n-tail-plus n)) ⟩
  headDelta (((n-tail n) ∙ tailDelta) (delta (headDelta d) (bind ds tailDelta))) ≡⟨ refl ⟩
  headDelta (n-tail n (bind ds tailDelta)) ≡⟨ monad-law-1-4 (S O) n ds ⟩
  headDelta (n-tail (S n) (headDelta (n-tail n ds))) ≡⟨ refl ⟩
  headDelta (n-tail (S n) (headDelta (((n-tail n) ∙ tailDelta) (delta d ds)))) ≡⟨ cong (\t -> headDelta (n-tail (S n) (headDelta (t (delta d ds))))) (n-tail-plus n)  ⟩
  headDelta (n-tail (S n) (headDelta (n-tail (S n) (delta d ds)))) ≡⟨ refl ⟩
  headDelta (n-tail (O + S n) (headDelta (n-tail (S n) (delta d ds))))
  ∎
monad-law-1-4 (S m) n (mono dd) = begin
  headDelta (n-tail n (bind (mono dd) (n-tail (S m)))) ≡⟨ refl ⟩
  headDelta (n-tail n ((n-tail (S m)) dd))≡⟨ cong (\t -> headDelta (t dd)) (n-tail-add {d = dd} n (S m)) ⟩
  headDelta (n-tail (n + S m) dd) ≡⟨ cong (\n -> headDelta ((n-tail n) dd)) (nat-add-sym n (S m)) ⟩
  headDelta (n-tail (S m + n) dd) ≡⟨ refl ⟩
  headDelta (n-tail (S m + n) (headDelta (mono dd))) ≡⟨ cong (\de -> headDelta (n-tail (S m + n) (headDelta de))) (sym (tail-delta-to-mono n dd)) ⟩
  headDelta (n-tail (S m + n) (headDelta (n-tail n (mono dd))))
  ∎
monad-law-1-4 (S m) O (delta d ds) = begin
  headDelta (n-tail O (bind (delta d ds) (n-tail (S m)))) ≡⟨ refl ⟩
  headDelta (bind (delta d ds) (n-tail (S m))) ≡⟨ refl ⟩
  headDelta (delta (headDelta ((n-tail (S m) d))) (bind ds (tailDelta ∙ (n-tail (S m))))) ≡⟨ refl ⟩
  headDelta (n-tail (S m) d) ≡⟨ cong (\n -> headDelta ((n-tail n) d)) (nat-add-right-zero (S m)) ⟩
  headDelta (n-tail (S m + O) d) ≡⟨ refl ⟩
  headDelta (n-tail (S m + O) (headDelta (delta d ds))) ≡⟨ refl ⟩
  headDelta (n-tail (S m + O) (headDelta (n-tail O (delta d ds))))
  ∎
monad-law-1-4 (S m) (S n) (delta d ds) = begin
  headDelta (n-tail (S n) (bind (delta d ds) (n-tail (S m)))) ≡⟨ refl ⟩
  headDelta (n-tail (S n) (delta (headDelta ((n-tail (S m)) d)) (bind ds (tailDelta ∙ (n-tail (S m)))))) ≡⟨ cong (\t -> headDelta (t (delta (headDelta ((n-tail (S m)) d)) (bind ds (tailDelta ∙ (n-tail (S m))))))) (sym (n-tail-plus n)) ⟩
  headDelta ((((n-tail n) ∙ tailDelta) (delta (headDelta ((n-tail (S m)) d)) (bind ds (tailDelta ∙ (n-tail (S m))))))) ≡⟨ refl ⟩
  headDelta (n-tail n (bind ds (tailDelta ∙ (n-tail (S m))))) ≡⟨ refl ⟩
  headDelta (n-tail n (bind ds  (n-tail (S (S m))))) ≡⟨ monad-law-1-4 (S (S m)) n ds ⟩
  headDelta (n-tail ((S (S m) +  n)) (headDelta (n-tail n ds))) ≡⟨ cong (\nm -> headDelta ((n-tail nm) (headDelta (n-tail n ds)))) (sym (nat-right-increment (S m) n))  ⟩
  headDelta (n-tail (S m + S n) (headDelta (n-tail n ds))) ≡⟨ refl ⟩
  headDelta (n-tail (S m + S n) (headDelta (((n-tail n) ∙ tailDelta) (delta d ds)))) ≡⟨ cong (\t -> headDelta (n-tail (S m + S n) (headDelta (t (delta d ds))))) (n-tail-plus n) ⟩
  headDelta (n-tail (S m + S n) (headDelta (n-tail (S n) (delta d ds))))
  ∎

monad-law-1-2 : {l : Level} {A : Set l} -> (d : Delta (Delta A)) -> headDelta (mu d) ≡ (headDelta (headDelta d))
monad-law-1-2 (mono _) = refl
monad-law-1-2 (delta _ _) = refl

monad-law-1-3 : {l : Level} {A : Set l} -> (n : Nat) -> (d : Delta (Delta (Delta A))) ->
  bind (fmap mu d) (n-tail n) ≡ bind (bind d (n-tail n)) (n-tail n)
monad-law-1-3 O (mono d)     = refl
monad-law-1-3 O (delta d ds) = begin
  bind (fmap mu (delta d ds)) (n-tail O) ≡⟨ refl ⟩
  bind (delta (mu d) (fmap mu ds)) (n-tail O) ≡⟨ refl ⟩
  delta (headDelta (mu d)) (bind (fmap mu ds) tailDelta) ≡⟨ cong (\dx -> delta dx (bind (fmap mu ds) tailDelta)) (monad-law-1-2 d) ⟩
  delta (headDelta (headDelta d)) (bind (fmap mu ds) tailDelta) ≡⟨ cong (\dx -> delta (headDelta (headDelta d)) dx) (monad-law-1-3 (S O) ds) ⟩
  delta (headDelta (headDelta d)) (bind (bind ds tailDelta) tailDelta) ≡⟨ refl ⟩
  bind (delta (headDelta d) (bind ds tailDelta)) (n-tail O) ≡⟨ refl ⟩
  bind (bind (delta d ds) (n-tail O)) (n-tail O)
  ∎
monad-law-1-3 (S n) (mono (mono d)) = begin
  bind (fmap mu (mono (mono d))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (mono d) (n-tail (S n)) ≡⟨ refl ⟩
  (n-tail (S n)) d ≡⟨ refl ⟩
  bind (mono d) (n-tail (S n)) ≡⟨ cong (\t -> bind t (n-tail (S n))) (sym (tail-delta-to-mono (S n) d))⟩
  bind (n-tail (S n) (mono d)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (n-tail (S n) (mono d)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (mono (mono d)) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (mono (delta d ds)) = begin
  bind (fmap mu (mono (delta d ds))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (mono (mu (delta d ds))) (n-tail (S n)) ≡⟨ refl ⟩
  n-tail (S n) (mu (delta d ds))  ≡⟨ refl ⟩
  n-tail (S n) (delta (headDelta d) (bind ds tailDelta))  ≡⟨ cong (\t -> t (delta (headDelta d) (bind ds tailDelta))) (sym (n-tail-plus n)) ⟩
  (n-tail n ∙ tailDelta) (delta (headDelta d) (bind ds tailDelta))  ≡⟨ refl ⟩
  n-tail n (bind ds tailDelta)  ≡⟨ monad-law-1-5 (S O) n ds ⟩
  bind (n-tail n ds) (n-tail (S n)) ≡⟨ refl ⟩
  bind (((n-tail n) ∙ tailDelta) (delta d ds)) (n-tail (S n)) ≡⟨ cong (\t -> (bind (t (delta d ds)) (n-tail (S n))))  (n-tail-plus n) ⟩
  bind (n-tail (S n) (delta d ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (mono (delta d ds)) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (delta (mono d) ds) = begin
  bind (fmap mu (delta (mono d) ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (delta (mu (mono d)) (fmap mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (delta d (fmap mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (bind (fmap mu ds) (n-tail (S (S n)))) ≡⟨ cong (\de -> delta (headDelta ((n-tail (S n)) d)) de) (monad-law-1-3 (S (S n)) ds) ⟩
  delta (headDelta ((n-tail (S n)) d)) (bind (bind ds (n-tail (S (S n)))) (n-tail (S (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (bind (bind ds (tailDelta ∙ (n-tail (S n))))  (n-tail (S (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) d)) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (mono d)))) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ cong (\de -> delta (headDelta ((n-tail (S n)) (headDelta de))) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n))))) (sym (tail-delta-to-mono (S n) d)) ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) (mono d))))) (bind (bind ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙  (n-tail (S n)))) ≡⟨ refl ⟩
  bind (delta (headDelta ((n-tail (S n)) (mono d))) (bind ds (tailDelta ∙ (n-tail (S n))))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (delta (mono d) ds) (n-tail (S n))) (n-tail (S n))
  ∎
monad-law-1-3 (S n) (delta (delta d dd) ds) = begin
  bind (fmap mu (delta (delta d dd) ds)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (delta (mu (delta d dd)) (fmap mu ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (mu (delta d dd)))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (delta (headDelta d) (bind dd tailDelta)))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ cong (\t -> delta (headDelta (t (delta (headDelta d) (bind dd tailDelta)))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))))(sym (n-tail-plus n)) ⟩
  delta (headDelta (((n-tail n) ∙ tailDelta) (delta (headDelta d) (bind dd tailDelta)))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail n) (bind dd tailDelta))) (bind (fmap mu ds) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail n) (bind dd tailDelta))) (bind (fmap mu ds) (n-tail (S (S n)))) ≡⟨ cong (\de -> delta (headDelta ((n-tail n) (bind dd tailDelta))) de) (monad-law-1-3 (S (S n)) ds) ⟩
  delta (headDelta ((n-tail n) (bind dd tailDelta))) (bind (bind  ds (n-tail (S (S n))))  (n-tail (S (S n)))) ≡⟨ cong (\de -> delta de ( (bind (bind  ds (n-tail (S (S n))))  (n-tail (S (S n)))))) (monad-law-1-4 (S O) n dd) ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (n-tail n dd)))) (bind (bind  ds (n-tail (S (S n))))  (n-tail (S (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (n-tail n dd)))) (bind (bind  ds (n-tail (S (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (n-tail n dd)))) (bind (bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n)) (headDelta (((n-tail n) ∙ tailDelta) (delta d dd))))) (bind (bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ cong (\t -> delta (headDelta ((n-tail (S n)) (headDelta (t (delta d dd))))) (bind (bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n))))) (n-tail-plus n) ⟩
  delta (headDelta ((n-tail (S n)) (headDelta ((n-tail (S n)) (delta d dd))))) (bind (bind  ds (tailDelta ∙ (n-tail (S n)))) (tailDelta ∙ (n-tail (S n)))) ≡⟨ refl ⟩
  bind (delta (headDelta ((n-tail (S n)) (delta d dd))) (bind  ds (tailDelta ∙ (n-tail (S n))))) (n-tail (S n)) ≡⟨ refl ⟩
  bind (bind (delta (delta d dd) ds) (n-tail (S n))) (n-tail (S n))
  ∎


-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) d) ≡ ((mu ∙ mu) d)
monad-law-1 (mono d)    = refl
monad-law-1 (delta x d) = begin
  (mu ∙ fmap mu) (delta x d)
  ≡⟨ refl ⟩
  mu (fmap mu (delta x d))
  ≡⟨ refl ⟩
  mu (delta (mu x) (fmap mu d))
  ≡⟨ refl ⟩
  delta (headDelta (mu x)) (bind (fmap mu d) tailDelta)
  ≡⟨ cong (\x -> delta x (bind (fmap mu d) tailDelta)) (monad-law-1-2 x) ⟩
  delta (headDelta (headDelta x)) (bind (fmap mu d) tailDelta)
  ≡⟨ cong (\d -> delta (headDelta (headDelta x)) d) (monad-law-1-3 (S O) d) ⟩
  delta (headDelta (headDelta x)) (bind (bind d tailDelta) tailDelta)
  ≡⟨ refl ⟩
  mu (delta (headDelta x) (bind d tailDelta))
  ≡⟨ refl ⟩
  mu (mu (delta x d))
  ≡⟨ refl ⟩
  (mu ∙ mu) (delta x d)
  ∎


-}

monad-law-2-1 : {l : Level} {A : Set l} -> (n : Nat) -> (d : Delta A) -> (bind (fmap eta d) (n-tail n)) ≡ d
monad-law-2-1 O (mono x)    = refl
monad-law-2-1 O (delta x d) = begin
  bind (fmap eta (delta x d)) (n-tail O)                  ≡⟨ refl ⟩
  bind (delta (eta x) (fmap eta d)) id                    ≡⟨ refl ⟩
  delta (headDelta (eta x)) (bind (fmap eta d) tailDelta) ≡⟨ refl ⟩
  delta x (bind (fmap eta d) tailDelta)                   ≡⟨ cong (\de -> delta x de) (monad-law-2-1 (S O) d) ⟩
  delta x d                                               ∎
monad-law-2-1 (S n) (mono x) = begin
  bind (fmap eta (mono x)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (mono (mono x)) (n-tail (S n))     ≡⟨ refl ⟩
  n-tail (S n) (mono x)                   ≡⟨ tail-delta-to-mono (S n) x ⟩
  mono x                                  ∎
monad-law-2-1 (S n) (delta x d) = begin
  bind (fmap eta (delta x d)) (n-tail (S n))                                                   ≡⟨ refl ⟩
  bind (delta (eta x) (fmap eta d)) (n-tail (S n))                                             ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n) (eta x)))) (bind (fmap eta d) (tailDelta ∙  (n-tail (S n)))) ≡⟨ refl ⟩
  delta (headDelta ((n-tail (S n) (eta x)))) (bind (fmap eta d) (n-tail (S (S n))))            ≡⟨ cong (\de -> delta (headDelta (de)) (bind (fmap eta d) (n-tail (S (S n))))) (tail-delta-to-mono (S n) x) ⟩
  delta (headDelta (eta x)) (bind (fmap eta d) (n-tail (S (S n))))                             ≡⟨ refl ⟩
  delta x (bind (fmap eta d) (n-tail (S (S n))))                                               ≡⟨ cong (\d -> delta x d) (monad-law-2-1 (S (S n)) d) ⟩
  delta x d
  ∎


-- monad-law-2 : join . fmap return = join . return = id
-- monad-law-2 join . fmap return = join . return
monad-law-2 : {l : Level} {A : Set l} -> (d : Delta A) ->
  (mu ∙ fmap eta) d ≡ (mu ∙ eta) d
monad-law-2 (mono x)    = refl
monad-law-2 (delta x d) = begin
  (mu ∙ fmap eta) (delta x d)                              ≡⟨ refl ⟩
  mu (fmap eta (delta x d))                                ≡⟨ refl ⟩
  mu (delta (mono x) (fmap eta d))                         ≡⟨ refl ⟩
  delta (headDelta (mono x)) (bind (fmap eta d) tailDelta) ≡⟨ refl ⟩
  delta x (bind (fmap eta d) tailDelta)                    ≡⟨ cong (\d -> delta x d) (monad-law-2-1 (S O) d) ⟩
  (delta x d)                                              ≡⟨ refl ⟩
  mu (mono (delta x d))                                    ≡⟨ refl ⟩
  mu (eta (delta x d))                                     ≡⟨ refl ⟩
  (mu ∙ eta) (delta x d)
  ∎


-- monad-law-2' :  join . return = id
monad-law-2' : {l : Level} {A : Set l} -> (d : Delta A) -> (mu ∙ eta) d ≡ id d
monad-law-2' d = refl


-- monad-law-3 : return . f = fmap f . return
monad-law-3 : {l : Level} {A B : Set l} (f : A -> B) (x : A) -> (eta ∙ f) x ≡ (fmap f ∙ eta) x
monad-law-3 f x = refl


monad-law-4-1 : {l ll : Level} {A : Set l} {B : Set ll} -> (n : Nat) -> (f : A -> B) -> (ds : Delta (Delta A)) ->
  bind (fmap (fmap f) ds) (n-tail n) ≡ fmap f (bind ds (n-tail n))
monad-law-4-1 O f (mono d)     = refl
monad-law-4-1 O f (delta d ds) = begin
  bind (fmap (fmap f) (delta d ds)) (n-tail O)                     ≡⟨ refl ⟩
  bind (delta (fmap f d) (fmap (fmap f) ds)) (n-tail O)            ≡⟨ refl ⟩
  delta (headDelta (fmap f d)) (bind (fmap (fmap f) ds) tailDelta) ≡⟨ cong (\de -> delta de (bind (fmap (fmap f) ds) tailDelta)) (head-delta-natural-transformation f d) ⟩
  delta (f (headDelta d))      (bind (fmap (fmap f) ds) tailDelta) ≡⟨ cong (\de -> delta (f (headDelta d)) de) (monad-law-4-1 (S O) f ds) ⟩
  delta (f (headDelta d))      (fmap f (bind ds tailDelta))        ≡⟨ refl ⟩
  fmap f (delta (headDelta d) (bind ds tailDelta))                 ≡⟨ refl ⟩
  fmap f (bind (delta d ds) (n-tail O))                            ∎
monad-law-4-1 (S n) f (mono d) = begin
  bind (fmap (fmap f) (mono d)) (n-tail (S n)) ≡⟨ refl ⟩
  bind (mono (fmap f d)) (n-tail (S n))        ≡⟨ refl ⟩
  n-tail (S n) (fmap f d)                      ≡⟨ n-tail-natural-transformation (S n) f d ⟩
  fmap f (n-tail (S n) d)                      ≡⟨ refl ⟩
  fmap f (bind (mono d) (n-tail (S n)))
  ∎
monad-law-4-1 (S n) f (delta d ds) = begin
  bind (fmap (fmap f) (delta d ds)) (n-tail (S n)) ≡⟨ refl ⟩
  delta (headDelta (n-tail (S n) (fmap f d))) (bind (fmap (fmap f) ds) (tailDelta ∙ (n-tail (S n))))  ≡⟨ refl ⟩
  delta (headDelta (n-tail (S n) (fmap f d))) (bind (fmap (fmap f) ds) (n-tail (S (S n))))            ≡⟨ cong (\de ->   delta (headDelta de) (bind (fmap (fmap f) ds) (n-tail (S (S n))))) (n-tail-natural-transformation (S n) f d) ⟩
  delta (headDelta (fmap f ((n-tail (S n) d)))) (bind (fmap (fmap f) ds) (n-tail (S (S n))))          ≡⟨ cong (\de -> delta de (bind (fmap (fmap f) ds) (n-tail (S (S n))))) (head-delta-natural-transformation f (n-tail (S n) d)) ⟩
  delta (f (headDelta (n-tail (S n) d))) (bind (fmap (fmap f) ds) (n-tail (S (S n))))                 ≡⟨ cong (\de -> delta (f (headDelta (n-tail (S n) d))) de) (monad-law-4-1 (S (S n)) f ds) ⟩
  delta (f (headDelta (n-tail (S n) d))) (fmap f (bind ds (n-tail (S (S n)))))                        ≡⟨ refl ⟩
  fmap f (delta (headDelta (n-tail (S n) d)) (bind ds (n-tail (S (S n)))))                            ≡⟨ refl ⟩
  fmap f (delta (headDelta (n-tail (S n) d)) (bind ds (tailDelta ∙ (n-tail (S n)))))                  ≡⟨ refl ⟩
  fmap f (bind (delta d ds) (n-tail (S n)))                                                           ∎


-- monad-law-4 : join . fmap (fmap f) = fmap f . join
monad-law-4 : {l ll : Level} {A : Set l} {B : Set ll} (f : A -> B) (d : Delta (Delta A)) ->
              (mu ∙ fmap (fmap f)) d ≡ (fmap f ∙ mu) d
monad-law-4 f (mono d)     = refl
monad-law-4 f (delta (mono x) ds) = begin
  (mu ∙ fmap (fmap f)) (delta (mono x) ds)                           ≡⟨ refl ⟩
  mu ( fmap (fmap f) (delta (mono x) ds))                            ≡⟨ refl ⟩
  mu (delta (mono (f x)) (fmap (fmap f) ds))                         ≡⟨ refl ⟩
  delta (headDelta (mono (f x))) (bind (fmap (fmap f) ds) tailDelta) ≡⟨ refl ⟩
  delta (f x) (bind (fmap (fmap f) ds) tailDelta)                    ≡⟨ cong (\de -> delta (f x) de) (monad-law-4-1 (S O) f ds) ⟩
  delta (f x) (fmap f (bind ds tailDelta))                           ≡⟨ refl ⟩
  fmap f (delta x (bind ds tailDelta))                               ≡⟨ refl ⟩
  fmap f (delta (headDelta (mono x)) (bind ds tailDelta))            ≡⟨ refl ⟩
  fmap f (mu (delta (mono x) ds))                                    ≡⟨ refl ⟩
  (fmap f ∙ mu) (delta (mono x) ds)                                  ∎
monad-law-4 f (delta (delta x d) ds) = begin
  (mu ∙ fmap (fmap f)) (delta (delta x d) ds)                                     ≡⟨ refl ⟩
  mu (fmap (fmap f) (delta (delta x d) ds))                                       ≡⟨ refl ⟩
  mu  (delta (delta (f x) (fmap f d)) (fmap (fmap f) ds))                         ≡⟨ refl ⟩
  delta (headDelta (delta (f x) (fmap f d)))  (bind (fmap (fmap f) ds) tailDelta) ≡⟨ refl ⟩
  delta (f x)  (bind (fmap (fmap f) ds) tailDelta)                                ≡⟨ cong (\de -> delta (f x) de) (monad-law-4-1 (S O) f ds) ⟩
  delta (f x) (fmap f (bind  ds tailDelta))                                       ≡⟨ refl ⟩
  fmap f (delta x (bind  ds tailDelta))                                           ≡⟨ refl ⟩
  fmap f (delta (headDelta (delta x d)) (bind  ds tailDelta))                     ≡⟨ refl ⟩
  fmap f (mu (delta (delta x d) ds))                                              ≡⟨ refl ⟩
  (fmap f ∙ mu) (delta (delta x d) ds) ∎



{-
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
monad-law-h-3 (delta x d) k h = {!!}

-}
