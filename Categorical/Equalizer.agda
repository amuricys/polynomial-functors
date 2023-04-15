{-# OPTIONS --cubical #-}

module Categorical.Equalizer where

open import Categorical.CubicalPoly
open import Categories.Category.Instance.Sets
open import Categories.Diagram.Equalizer Poly
open import Level
open import Categories.Diagram.Coequalizer (Sets zero)
open import CategoryData.Everything
open import Cubical.ArrowEquals
open import Cubical.Foundations.Prelude
open import Data.Sum
open import Data.Product using (_×_)
open import Cubical.Data.Equality
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Isomorphism
open import Function

data Coeq {A B : Set} (f g : A → B) : Set where
  inc    : B → Coeq f g
  glue   : ∀ x → inc (f x) ≡ inc (g x)
  squash : isSet (Coeq f g)
open Coeq

open Polynomial
eq : {p q : Polynomial} → (f g : Arrow p q) → Equalizer f g
eq {p} {q} f@(mpf ⇄ mdf) g@(mpg ⇄ mdg) = 
  record {
    obj = eqObj ;
    arr = arr ; 
    isEqualizer = isEqualizer
    }
   where EqualizedPosition = Σ (position p) (λ z → mpf z ≡c mpg z)
         eqObj : Polynomial
         eqObj = MkPoly EqualizedPosition (λ ( i , equal ) → Coeq (mdf i) (subst (λ x → direction q x → direction p i) (sym equal) (mdg i)))
         arr : Arrow eqObj p
         arr = mp ⇄ md
            where mp : position eqObj → position p
                  mp (i , _) = i
                  md : (fromPos : position eqObj) → direction p (mp fromPos) → direction eqObj fromPos
                  md fromPos dir = inc dir
         isEqualizer : IsEqualizer arr f g
         isEqualizer = record { 
            equality = arrow≡∀∀ mapPos≡ mapDir≡;
            equalize = λ {X} {h@(hPos ⇄ hDir)} x  →  equalize {X} {h} x ; 
            universal = {!   !} ; 
            unique = {!   !} }
              where equalize : {X : Polynomial} {h : Arrow X p} → (x : f ∘ₚ h ≡ g ∘ₚ h) → Arrow X eqObj 
                    equalize {X} {h@(hPos ⇄ hDir)} x = let
                              arrPos = Arrow.mapPosition arr
                              arrDir = Arrow.mapDirection arr
                              mpf∘hPos≡mpg∘hPos : mpf ∘ hPos ≡ mpg ∘ hPos
                              mpf∘hPos≡mpg∘hPos = λ i → Arrow.mapPosition (x i)
                              in (λ x₁ → hPos x₁ , λ i → mpf∘hPos≡mpg∘hPos i x₁) ⇄ λ { fromPos (inc x) → hDir fromPos x
                                                                                    ; fromPos (glue smth i) → {!   !}
                                                                                    ; fromPos (squash x₁ x₂ x y i i₃) → {!   !} }
                    mapPos≡ : (λ x → mpf (fst x)) ≡c (λ x → mpg (fst x))
                    mapPos≡ = funExt snd
                    mapDir≡ : (fromPos : EqualizedPosition) →
                              (dirQFromG : direction q (mpg (fst fromPos))) →
                              let canonicalDirQ = subst (λ x → direction q x → direction p (fst fromPos)) (sym (snd fromPos)) (mdg (fst fromPos))
                                  typeOfMapDirGivenMapPos : (EqualizedPosition → position q) → Set
                                  typeOfMapDirGivenMapPos h = 
                                    (x : EqualizedPosition) → 
                                    direction q (h x) → 
                                    Coeq (mdf (fst x)) (subst (λ x₁ → direction q x₁ → direction p (fst x)) (sym (snd x)) (mdg (fst x)))
                                  substed = subst typeOfMapDirGivenMapPos mapPos≡ (λ fromPos₁ z → mapDirection arr fromPos₁ (mdf (mapPosition arr fromPos₁) z)) 
                              in
                              substed fromPos dirQFromG
                              ≡c
                              mapDirection arr fromPos (mdg (mapPosition arr fromPos) dirQFromG)
                    mapDir≡ fromPos dirQFromG = {!   !}

import Categories.Diagram.Equalizer (Sets zero) as SetsEq
eqSets : {A B : Set} → (f g : A → B) → SetsEq.Equalizer f g
eqSets {A} {B} f g = record { 
      obj = (Σ[ i ∈ A ] (f i ≡p g i)) ;
      arr = λ { (fst₁ , snd₁) → fst₁ } ; 
      isEqualizer = record { 
            equality = \{ {fst₁ , snd₁} → snd₁ }; 
            equalize = λ {X} {h} x x₁ → h x₁ , x ; 
            universal =  reflp ; 
            unique = unique }
            }
            where unique : {eqSet : Type} → 
                           {eqArr : eqSet → A} → 
                           {eq : eqSet → Σ[ i ∈ A ] (f i ≡p g i) } → 
                           {a : {x = x₁ : eqSet} → f (eqArr x₁) ≡p g (eqArr x₁)} → 
                           (y : {x = x₁ : eqSet} → eqArr x₁ ≡p fst (eq x₁)) →
                           {x : eqSet} →
                           eq x ≡p (eqArr x , a)
                  unique {eqSet} {eqArr} {eq} {a} y {x} = let
                        anew , pro = eq x
                        res = eqArr x
                        hmm = ptoc (a {x})
                        hmm2 = ptoc (y {x})
                        lemma : fst (eq x) ≡c eqArr x
                        lemma = sym hmm2
                        lemma22 : eqArr x ≡c fst (eq x)
                        lemma22 = sym lemma
                        lemma2 : ctop {!   !} ≡c a {x}
                        lemma2 = {!   !}
                        in
                          ctop {!   !}


open Coeq
coeqSets : {A B : Set} → (f g : A → B) → Coequalizer f g
coeqSets {A} {B} f g = record { 
      obj = Coeq f g ; 
      arr = λ x → inc x; 
      isCoequalizer = record { 
            equality = \{x} → ctop (glue x) ; 
            coequalize = λ { {coeqSet} {h} x x₁ → coequalize {coeqSet} {h} x x₁ }; 
            universal = reflp ; 
            unique = {!   !} 
            }
      }
  where coequalize : {coeqSetCandidate : Set} →
                     {h : B → coeqSetCandidate} →
                     (x : {x = x₂ : A} → h (f x₂) ≡p h (g x₂)) →
                     (coeqSetElmt : Coeq f g) → 
                     coeqSetCandidate
        coequalize {coeqSetCandidate} {h} x (inc x₁) = h x₁
        coequalize {coeqSetCandidate} {h} x (glue x₁ i) = ptoc (x {x₁}) i
        coequalize {coeqSetCandidate} {h} x (squash coeqSetElmt coeqSetElmt₁ x₁ y i i₃) = {!  !}


-- (Σ[ i ∈ p.position ] (p.direction i → q.position))
-- p'(1) := {i ∈ p(1) | mpf(i) = mpg(i)}
       