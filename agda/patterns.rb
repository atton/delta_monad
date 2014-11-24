#!/usr/bin/env ruby

require 'pry'

# Agda {{{

Agda = %q(
open import list
open import basic

open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module hoge where


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
{-
monad-law-1-sub : {l : Level} {A : Set l} -> (x : Delta (Delta A)) (d : Delta (Delta (Delta A)))
  -> deltaAppend (headDelta (bind x id)) (bind (fmap mu d) (tailDelta ∙ id)) ≡ bind (deltaAppend (headDelta x) (bind d (tailDelta ∙ id))) id
monad-law-1-sub (mono x) (mono (mono (mono x₁))) = refl
monad-law-1-sub (mono x) (mono (mono (delta x₁ d))) = refl
monad-law-1-sub (mono x) (mono (delta d d1)) = begin
  deltaAppend (headDelta (bind (mono x) id)) (bind (fmap mu (mono (delta d d1))) (tailDelta ∙ id))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (bind (mono x) id)) (bind ((mono (mu (delta d d1)))) (tailDelta ∙ id))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (bind (mono x) id)) (bind (mono (bind (delta d d1) id)) (tailDelta ∙ id))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu (mono x))) (((tailDelta ∙ id) (mu (delta d d1))))
  ≡⟨ refl ⟩
  deltaAppend (headDelta (mu (mono x))) (((tailDelta ∙ id) (bind (delta d d1) id)))
  ≡⟨ {!!} ⟩
  deltaAppend (headDelta (mu (mono x))) (((tailDelta ∙ id) (bind (delta d d1) id)))
--  bind (delta (mu (mono x)) (mono (mu (delta d d1)))) id
  ≡⟨ {!!} ⟩
  bind (deltaAppend (headDelta (mono x)) (bind (mono (delta d d1)) (tailDelta ∙ id))) id
  ∎
monad-law-1-sub (delta x x₁) (mono d) = {!!}
monad-law-1-sub x (delta d d1) = begin
  deltaAppend (headDelta (bind x id)) (bind (fmap mu (delta d d1)) (tailDelta ∙ id))
  ≡⟨ {!!} ⟩
  bind (deltaAppend (headDelta x) (bind (delta d d1) (tailDelta ∙ id))) id
  ∎

-}
-- monad-law-1 : join . fmap join = join . join
monad-law-1 : {l : Level} {A : Set l} -> (d : Delta (Delta (Delta A))) -> ((mu ∙ (fmap mu)) d) ≡ ((mu ∙ mu) d)
)

# }}}

Rules    = {
    'T3' => ['(mono T2)', '(delta T2 T3)'],
    'T2' => ['(mono T1)', '(delta T1 T2)'],
    'T1' => ['(mono _)',  '(delta _ T1)']
}

def generate_patterns source_patterns, operations
  patterns = source_patterns.clone
  operations.each do |op|
    patterns = Rules[op].flat_map do |r|
      patterns.flat_map{|p| p.gsub(op, r)}
    end
  end
  patterns.uniq
end

def pattern_formatter non_format_patterns
  formatted_patterns = non_format_patterns.clone

  Rules.keys.each do |k|
    formatted_patterns.map!{|p| p.gsub(k, '_')}
  end

  formatted_patterns
end

def generate_function function_name, patterns, body
  patterns.map do |p|
    "#{function_name} #{p} = #{body}"
  end
end

def generate_agda function_body
  Agda + function_body.join("\n")
end



patterns   = ['(mono _)', '(delta T2 T3)']
operations = ['T3'].cycle(3).to_a + ['T2'].cycle(6).to_a + ['T1'].cycle(12).to_a


patterns = generate_patterns(patterns, operations)

puts patterns.size
function_body = generate_function('monad-law-1', pattern_formatter(patterns), 'refl')
agda          = generate_agda(function_body)
File.open('hoge.agda', 'w').write(agda)
