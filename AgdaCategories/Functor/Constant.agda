{-# OPTIONS --cubical #-}

module AgdaCategories.Functor.Constant where

import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Unit
open import Data.Empty
open import Level
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation renaming ( id to idN )
open import Cubical.Data.Equality using (ctop ; ptoc)
open import Cubical.Foundations.Prelude
open import Common.CategoryData
open import Function
open import Function.Surjection hiding (id)
open import AgdaCategories.CubicalPoly
open import Cubical.Proofs
open import Data.Bool

-- Fully faithful functor sending a set A to the constant polynomial Ay^0 = A
constantPolynomial : Functor (Sets Level.zero) Poly 
constantPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → ⊥
    ; F₁ = λ f → f ⇄ λ fromPos → id
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ p → arrowsEqual (funExt λ x → ptoc p) refl
    }

why : {posA posB : Set} (f : Arrow (MkPolynomial posA (λ _ → ⊥)) (MkPolynomial posB (λ _ → ⊥))) → (Arrow.mapPosition f ⇄ (λ fromPos x₁ → x₁)) ≡ f
why {posA} {posB} (mapPosition ⇄ mapDirection) = λ i → mapPosition ⇄ λ fromPos -> {!   !}

full : Full constantPolynomial
full = record 
    { from = record 
        { _⟨$⟩_ = Arrow.mapPosition
        ; cong = positionArrowsEqualPwiseEq } 
    ; right-inverse-of = why
    }

faithful : Faithful constantPolynomial
faithful = λ f g x → ctop (positionArrowsEqualPwise x)
ffcp : FullyFaithful constantPolynomial
ffcp = full , faithful