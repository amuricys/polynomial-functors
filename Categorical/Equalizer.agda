{-# OPTIONS --cubical #-}

module Categorical.Equalizer where

open import Categorical.CubicalPoly
open import Categories.Diagram.Equalizer Poly
open import Common.CategoryData
open import Cubical.ArrowEquals
open import Cubical.Foundations.Prelude
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
         equalizerObject = MkPolynomial (Σ[ i ∈ position p ] (mpf i ≡ mpg i)) dir
            where dir : (Σ[ i ∈ position p ] (mpf i ≡ mpg i)) → Set
                  dir ( i , _ ) = coeq (mdf i) (mdf i) -- we can do this because the positions are equalized, so the domain of the direction coequalizer is equal
                    where coeq : {i : position p} → (f g : direction q (mpf i) → direction p i) → Set
                          coeq {i} f g = Σ[ b ∈ direction p i ] ((a : direction q (mpf i)) → (f a ≡ b) × (g a ≡ b))
         arr : Arrow equalizerObject p
         arr = mp ⇄ md
            where mp : position equalizerObject → position p
                  mp (i , _) = i
                  md : (fromPos : position equalizerObject) → direction p (mp fromPos) → direction equalizerObject fromPos
                  md (i , snd₁) dir = dir , λ a → {!   !} -- gotta subst snd₁ in here somehow

-- (Σ[ i ∈ p.position ] (p.direction i → q.position))
-- p'(1) := {i ∈ p(1) | mpf(i) = mpg(i)}
