open import Level
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open import basic
open import delta
open import delta.functor
open import delta.monad
open import deltaM
open import deltaM.functor
open import nat
open import laws

module deltaM.monad where
open Functor
open NaturalTransformation
open Monad


-- sub proofs 

fmap-headDeltaM-with-deltaM-eta : {l : Level} {A : Set l} {n : Nat}
                                  {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM}
  (x : M A) ->  (fmap functorM ((headDeltaM {l} {A} {n} {M} {functorM} {monadM}) ∙ deltaM-eta) x) ≡ fmap functorM (eta monadM) x
fmap-headDeltaM-with-deltaM-eta {l} {A} {O} {M} {fm} {mm}    x = refl
fmap-headDeltaM-with-deltaM-eta {l} {A} {S n} {M} {fm} {mm} x  = refl


fmap-tailDeltaM-with-deltaM-eta : {l : Level} {A : Set l} {n : Nat}
                   {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM}
                   (d : DeltaM M {functorM} {monadM} A (S n)) ->
       deltaM-fmap ((tailDeltaM {n = n} {monadM = monadM} )  ∙ deltaM-eta) d ≡ deltaM-fmap (deltaM-eta) d
fmap-tailDeltaM-with-deltaM-eta {n = O} d = refl
fmap-tailDeltaM-with-deltaM-eta {n = S n} d = refl


-- main proofs

postulate deltaM-eta-is-nt : {l : Level} {A B : Set l} {n : Nat}
                   {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM} 
                   (f : A -> B) -> (x : A) ->
                   ((deltaM-eta {l} {B} {n} {M} {functorM} {monadM} )∙ f) x ≡ deltaM-fmap f (deltaM-eta x)
{-
deltaM-eta-is-nt {l} {A} {B} {O} {M} {fm} {mm} f x   = begin
  deltaM-eta {n = O} (f x)              ≡⟨ refl ⟩
  deltaM (mono (eta mm (f x)))          ≡⟨ cong (\de -> deltaM (mono de)) (eta-is-nt mm f x) ⟩
  deltaM (mono (fmap fm f (eta mm x)))  ≡⟨ refl ⟩
  deltaM-fmap f (deltaM-eta {n = O} x)  ∎
deltaM-eta-is-nt {l} {A} {B} {S n} {M} {fm} {mm} f x = begin
  deltaM-eta {n = S n} (f x) ≡⟨ refl ⟩
  deltaM (delta-eta {n = S n} (eta mm (f x))) ≡⟨ refl ⟩
  deltaM (delta (eta mm (f x)) (delta-eta (eta mm (f x))))
  ≡⟨ cong (\de -> deltaM (delta de (delta-eta de))) (eta-is-nt mm f x) ⟩
  deltaM (delta (fmap fm f (eta mm x)) (delta-eta (fmap fm f (eta mm x))))
  ≡⟨ cong (\de ->  deltaM (delta (fmap fm f (eta mm x)) de)) (eta-is-nt delta-is-monad (fmap fm f) (eta mm x)) ⟩
  deltaM (delta (fmap fm f (eta mm x)) (delta-fmap (fmap fm f) (delta-eta (eta mm x))))
  ≡⟨ refl ⟩
  deltaM-fmap f (deltaM-eta {n = S n} x)
  ∎
-}

postulate  deltaM-right-unity-law : {l : Level} {A : Set l}
                         {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM} {n : Nat}
                         (d : DeltaM M {functorM} {monadM} A (S n)) -> (deltaM-mu ∙ deltaM-eta) d ≡ id d
{-
deltaM-right-unity-law {l} {A} {M} {fm} {mm} {O} (deltaM (mono x)) = begin
  deltaM-mu (deltaM-eta (deltaM (mono x)))             ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (eta mm (deltaM (mono x))))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (headDeltaM {M = M})(eta mm (deltaM (mono x))))))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (sym (eta-is-nt mm headDeltaM (deltaM (mono x)) )) ⟩
  deltaM (mono (mu mm (eta mm ((headDeltaM {l} {A} {O} {M} {fm} {mm}) (deltaM (mono x)))))) ≡⟨ refl ⟩
  deltaM (mono (mu mm (eta mm x))) ≡⟨ cong (\de -> deltaM (mono de)) (sym (right-unity-law mm x)) ⟩
  deltaM (mono x)
  ∎
deltaM-right-unity-law {l} {A} {M} {fm} {mm} {S n} (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-eta (deltaM (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (eta mm (deltaM (delta x d))) (delta-eta (eta mm (deltaM (delta x d))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm (headDeltaM {monadM = mm}) (eta mm (deltaM (delta x d)))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono (mu mm de)))
                                (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d))))))))
           (sym (eta-is-nt mm headDeltaM (deltaM (delta x d)))) ⟩
  appendDeltaM (deltaM (mono (mu mm (eta mm ((headDeltaM {monadM = mm}) (deltaM (delta x d)))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (eta mm x))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono de)) (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d))))))))
           (sym (right-unity-law mm x)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-fmap (fmap fm tailDeltaM) (delta-eta (eta mm (deltaM (delta x d)))))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM de))) (sym (eta-is-nt delta-is-monad (fmap fm tailDeltaM) (eta mm (deltaM (delta x d))))) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-eta (fmap fm tailDeltaM (eta mm (deltaM (delta x d)))))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-eta de)))) (sym (eta-is-nt mm tailDeltaM (deltaM (delta x d)))) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-eta (eta mm (tailDeltaM (deltaM (delta x d)))))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM (delta-eta (eta mm (deltaM d)))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-eta (deltaM d)))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) de) (deltaM-right-unity-law (deltaM d)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM d)
  ≡⟨ refl ⟩
  deltaM (delta x d)
  ∎
-}





postulate deltaM-left-unity-law : {l : Level} {A : Set l}
                        {M : Set l -> Set l} {functorM : Functor M} {monadM : Monad M functorM}
                        {n : Nat}
                        (d : DeltaM M {functorM} {monadM} A (S n)) ->
                              (deltaM-mu ∙ (deltaM-fmap deltaM-eta)) d ≡ id d
{-
deltaM-left-unity-law {l} {A} {M} {fm} {mm} {O} (deltaM (mono x))      = begin
  deltaM-mu (deltaM-fmap deltaM-eta (deltaM (mono x)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta-fmap (fmap fm deltaM-eta) (mono x)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (fmap fm deltaM-eta x)))
  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (headDeltaM {l} {A} {O} {M}) (fmap fm deltaM-eta x))))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (sym (covariant fm deltaM-eta headDeltaM x)) ⟩
  deltaM (mono (mu mm (fmap fm ((headDeltaM {l} {A} {O} {M} {fm} {mm}) ∙ deltaM-eta) x)))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (fmap-headDeltaM-with-deltaM-eta {l} {A} {O} {M} {fm} {mm} x) ⟩
  deltaM (mono (mu mm (fmap fm (eta mm) x)))
  ≡⟨ cong (\de -> deltaM (mono de)) (left-unity-law mm x) ⟩
  deltaM (mono x)
  ∎
deltaM-left-unity-law {l} {A} {M} {fm} {mm} {S n} (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-fmap deltaM-eta (deltaM (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta-fmap (fmap fm deltaM-eta) (delta x d)))
  ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (fmap fm deltaM-eta x) (delta-fmap (fmap fm deltaM-eta) d)))
  ≡⟨ refl  ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm (headDeltaM {l} {A} {S n} {M} {fm} {mm}) (fmap fm deltaM-eta x)))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono (mu mm de)))
                                (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d)))))
           (sym (covariant fm deltaM-eta headDeltaM x)) ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm ((headDeltaM {l} {A} {S n} {M} {fm} {mm}) ∙ deltaM-eta) x))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono (mu mm de)))
                                (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d)))))
           (fmap-headDeltaM-with-deltaM-eta {l} {A} {S n} {M} {fm} {mm} x) ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm (eta mm) x))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))

  ≡⟨ cong (\de -> (appendDeltaM (deltaM (mono de)) (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))))
           (left-unity-law mm x) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-eta) d))))
  ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap (tailDeltaM {n = n})(deltaM-fmap deltaM-eta (deltaM d))))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) (deltaM-mu de)) (sym (covariant deltaM-is-functor deltaM-eta tailDeltaM (deltaM d))) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap ((tailDeltaM {n = n}) ∙ deltaM-eta) (deltaM d)))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) (deltaM-mu de)) (fmap-tailDeltaM-with-deltaM-eta (deltaM d)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM-mu (deltaM-fmap deltaM-eta (deltaM d)))
  ≡⟨ cong (\de -> appendDeltaM (deltaM (mono x)) de) (deltaM-left-unity-law (deltaM d)) ⟩
  appendDeltaM (deltaM (mono x)) (deltaM d)
  ≡⟨ refl ⟩
  deltaM (delta x d)
  ∎

-}


fmap-headDeltaM-with-deltaM-mu : {l : Level} {A : Set l} {n : Nat}
                         {M : Set l -> Set l} {fm : Functor M} {mm : Monad M fm}
                         (x : M (DeltaM M {fm} {mm} (DeltaM M {fm} {mm} A (S n)) (S n))) ->
--                         (fmap fm headDeltaM (fmap fm deltaM-mu x)) ≡ (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x)))
--                         fmap fm (headDeltaM ∙ deltaM-mu) x ≡ fmap fm (fmap fm ((mu mm) ∙ (fmap fm headDeltaM))) x
                         headDeltaM (deltaM-fmap deltaM-mu (deltaM (mono x))) ≡ deltaM (mono (mu mm (fmap fm headDeltaM x)))
fmap-headDeltaM-with-deltaM-mu {l} {A} {O} {M} {fm} {mm} x = {!!}
fmap-headDeltaM-with-deltaM-mu {n = S n} x = {!!}

deltaM-mono : {l : Level} {A : Set l} 
                         {M : Set l -> Set l} {fm : Functor M} {mm : Monad M fm}
                         (d : M A) -> DeltaM M {fm} {mm} A (S O)
deltaM-mono x = deltaM (mono x)

fmap-headDeltaM-with-deltaM-mono : {l : Level} {A : Set l}
                         {M : Set l -> Set l} {fm : Functor M} {mm : Monad M fm}
                         (x : M (M A)) ->
                         fmap fm ((headDeltaM {l} {A} {O} {M} {fm} {mm}) ∙ deltaM-mono) x ≡ x
fmap-headDeltaM-with-deltaM-mono {fm = fm} x = preserve-id fm x




deltaM-association-law : {l : Level} {A : Set l} {n : Nat}
                         (M : Set l -> Set l) (fm : Functor M) (mm : Monad M fm)
                         (d : DeltaM M {fm} {mm} (DeltaM M {fm} {mm} (DeltaM M {fm} {mm} A (S n)) (S n))  (S n)) ->
                         deltaM-mu (deltaM-fmap deltaM-mu d) ≡ deltaM-mu (deltaM-mu d)
deltaM-association-law {l} {A} {O} M fm mm (deltaM (mono x))    = begin
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (mono x))) ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (fmap fm deltaM-mu x)))     ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x))))     ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm (\x -> (deltaM (mono (mu mm (fmap fm headDeltaM (headDeltaM x)))))) x))))  ≡⟨ refl ⟩

  deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm (\x -> (deltaM-mono (mu mm (fmap fm headDeltaM (headDeltaM x))))) x))))  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm (deltaM-mono ∙ (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x))))) x))))  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (((fmap fm (deltaM-mono)) ∙ (fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x)))))) x))))  ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mono (fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x)))) x))))) 
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (sym (covariant fm deltaM-mu headDeltaM x )) ⟩

  deltaM (mono (mu mm (fmap fm (headDeltaM ∙ deltaM-mono) ((fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x))))) x)))) 
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (fmap-headDeltaM-with-deltaM-mono ((fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x))))) x)) ⟩

  deltaM (mono (mu mm (fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x)))) x)))  ≡⟨ refl ⟩



{-
  {!!}



  deltaM (mono (mu mm (fmap fm (headDeltaM) (fmap fm 
  (\x -> ((deltaM (mono (mu mm (fmap fm (headDeltaM {l} {A} {O} {M} {fm} {mm} )(headDeltaM {l} {DeltaM M {fm} {mm} A (S O)} {O} {M} {fm} {mm} x))))))) x))))     ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm (\x -> ((deltaM-mono (mu mm (fmap fm headDeltaM (headDeltaM x)))))) x))))     ≡⟨ refl ⟩

  deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm (deltaM-mono ∙ (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x))))) x))))     ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (((fmap fm deltaM-mono) ∙ (fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x)))))) x))))     ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (((fmap fm deltaM-mono (fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x)))) x)))))))     ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm (headDeltaM ∙ deltaM-mono)  (fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x)))) x))))   
  ≡⟨ {!!} ⟩
--  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (fmap-headDeltaM-with-deltaM-eta (fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x)))) x)) ⟩
-}
  deltaM (mono (mu mm (fmap fm (\x -> (mu mm (fmap fm headDeltaM (headDeltaM x)))) x)))     ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm ((mu mm) ∙ (\x -> (fmap fm headDeltaM (headDeltaM x)))) x)))     ≡⟨ refl ⟩
  deltaM (mono (mu mm (fmap fm ((mu mm) ∙ ((fmap fm headDeltaM) ∙ headDeltaM)) x)))
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (covariant fm ((fmap fm headDeltaM) ∙ headDeltaM) (mu mm) x) ⟩
  deltaM (mono (mu mm (((fmap fm (mu mm)) ∙ (fmap fm ((fmap fm headDeltaM) ∙ headDeltaM))) x))) 
  ≡⟨ refl ⟩
   deltaM (mono (mu mm (fmap fm (mu mm)  ((fmap fm ((fmap fm headDeltaM) ∙ headDeltaM) x))) ))
  ≡⟨ cong (\de -> deltaM (mono (mu mm (fmap fm (mu mm)  de)))) (covariant fm headDeltaM (fmap fm headDeltaM) x) ⟩
  deltaM (mono (mu mm (fmap fm (mu mm) (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x)))))  
  ≡⟨ cong (\de -> deltaM (mono de)) (association-law mm (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x))) ⟩
  deltaM (mono (mu mm (mu mm (fmap fm (fmap fm headDeltaM) (fmap fm headDeltaM x)))))  
  ≡⟨ cong (\de -> deltaM (mono (mu mm de))) (mu-is-nt mm headDeltaM (fmap fm headDeltaM x)) ⟩
  deltaM (mono (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x)))))  ≡⟨ refl ⟩
  deltaM-mu (deltaM (mono (mu mm (fmap fm headDeltaM x))))  ≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (mono x)))
  ∎
deltaM-association-law {n = S n} M fm mm (deltaM (delta x d)) = begin
  deltaM-mu (deltaM-fmap deltaM-mu (deltaM (delta x d))) ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta-fmap (fmap fm deltaM-mu) (delta x d))) ≡⟨ refl ⟩
  deltaM-mu (deltaM (delta (fmap fm deltaM-mu x) (delta-fmap (fmap fm deltaM-mu) d))) ≡⟨ refl ⟩
  appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (fmap fm deltaM-mu x)))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM (delta-fmap (fmap fm deltaM-mu) d)))) ≡⟨ {!!} ⟩

  appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM (mu mm (fmap fm headDeltaM x))))))
               (deltaM-mu (deltaM-fmap tailDeltaM (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))) ≡⟨ {!!} ⟩
  deltaM-mu (appendDeltaM (deltaM (mono (mu mm (fmap fm headDeltaM x)))) 
                          (deltaM-mu (deltaM-fmap tailDeltaM (deltaM d))))≡⟨ refl ⟩
  deltaM-mu (deltaM-mu (deltaM (delta x d)))
  ∎




deltaM-is-monad : {l : Level} {A : Set l} {n : Nat}
                              {M : Set l -> Set l}
                              (functorM : Functor M)
                              (monadM   : Monad M functorM) ->
               Monad {l} (\A -> DeltaM M {functorM} {monadM} A (S n)) (deltaM-is-functor {l} {n})
deltaM-is-monad {l} {A} {n} {M} functorM monadM = 
                record { mu     = deltaM-mu;
                         eta    = deltaM-eta;
                         return = deltaM-eta;
                         bind   = deltaM-bind;
                         association-law = (deltaM-association-law M functorM monadM) ;
                         left-unity-law  = deltaM-left-unity-law;
                         right-unity-law = (\x -> (sym (deltaM-right-unity-law x))) ;
                         eta-is-nt = deltaM-eta-is-nt }


