{-# OPTIONS --cubical #-}

module Categorical.Equalizer where

open import Categorical.CubicalPoly
open import Categories.Diagram.Equalizer Poly
open import CategoryData.Core
open import Cubical.ArrowEquals
open import Cubical.Foundations.Prelude
open import Data.Sum
open import Data.Product using (_×_)

open Polynomial
eq : {p q : Polynomial} → (f g : Arrow p q) → Equalizer f g
eq {p} {q} (mpf ⇄ mdf) (mpg ⇄ mdg) = 
  record {
    obj = equalizerObject ;
    arr = arr ; 
    isEqualizer = {!   !} 
    }
   where equalizerObject : Polynomial
         equalizerObject = MkPoly (Σ[ i ∈ position p ] (mpf i ≡ mpg i)) dir
            where dir : (Σ[ i ∈ position p ] (mpf i ≡ mpg i)) → Set
                  dir ( i , equal ) = coeq (mdf i) (mdf i) -- we can do this because the positions are equalized, so the domain of the direction coequalizer is equal
                    where coeqConstraint : {i : position p} → (f g : direction q (mpf i) → direction p i) → direction p i → Set
                          coeqConstraint {i} f g b = ∀ (a₁ a₂ : direction q (mpf i)) → ((f a₁ ≡ b) × (g a₂ ≡ b)) → a₁ ≡ a₂
                          coeq : {i : position p} → (f g : direction q (mpf i) → direction p i) → Set
                          coeq {i} f g = Σ[ b ∈ direction p i ] (coeqConstraint f g b)
         arr : Arrow equalizerObject p
         arr = mp ⇄ md
            where mp : position equalizerObject → position p
                  mp (i , _) = i
                  md : (fromPos : position equalizerObject) → direction p (mp fromPos) → direction equalizerObject fromPos
                  md (i , mdfEq) d = d , λ { a a₂ (fst₁ , snd₁) → λ i₁ → {!   !} } -- gotta subst snd₁ in here somehow
-- eq {p} {q} f@(fₚ ⇄ f♯) g@(gₚ ⇄ g♯) = record { obj = equalizerObject ; arr = equalizerArrow ; isEqualizer = equalizerProof }
--       where
--             equalizerObject : Polynomial
--             equalizerObject = MkPolynomial pos dir
--                   where
--                         pos : Type
--                         pos = Σ[ i ∈ position p ] fₚ i ≡ gₚ i -- Equalizer of sets. All positions such that fₚ and gₚ equals.

--                         dir : pos → Type
--                         dir (posₚ , fₚposₚ≡gₚposₚ) = coeq (f♯ posₚ) (g♯ posₚ)
--                               where
--                                     coeq : {! (f g : direction q (fₚ posₚ) → direction p posₚ) → Type  !}
--                                     coeq = {!   !}

--             equalizerArrow : Arrow equalizerObject p
--             equalizerArrow = {!   !}

--             equalizerProof : IsEqualizer equalizerArrow f g
--             equalizerProof = record { equality = {!   !} ; equalize = {!   !} ; universal = {!   !} ; unique = {!   !} }







-- (Σ[ i ∈ p.position ] (p.direction i → q.position))
-- p'(1) := {i ∈ p(1) | mpf(i) = mpg(i)}
 