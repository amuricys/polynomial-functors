{-# OPTIONS --cubical #-}

module Categorical.Poly.Functor.Constant where

import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Unit
open import Data.Empty
open import Level
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation renaming ( id to idN )
open import Cubical.Data.Equality using (pathToEq ; eqToPath)
open import Cubical.Foundations.Prelude
open import CategoryData.Everything
open import Function
open import Categorical.Poly.Instance
open import Cubical.Proofs
open import Data.Bool
open import Cubical.LensEquality

fromAnythingToFalseToAnythingEqual : {A B : Set} {w z : A → ⊥ → B} → w ≡ z
fromAnythingToFalseToAnythingEqual i x ()

-- Fully faithful functor sending a set A to the constant polynomial Ay^0 = A
constantPolynomial : Functor (Sets Level.zero) Poly 
constantPolynomial = record
    { F₀ = λ x → mkpoly x λ _ → ⊥
    ; F₁ = λ f → f ⇆ λ fromPos → id
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ p → lensesEqual3 (funExt λ x → eqToPath p) λ x ()
    }

full : Full constantPolynomial
full = record 
    { from = record 
        { _⟨$⟩_ = Lens.mapPosition
        ; cong = positionLensesEqualPwiseEq } 
    ; right-inverse-of = \_ → lensesEqual3 refl λ x ()
    }

faithful : Faithful constantPolynomial
faithful = λ f g x → pathToEq (positionLensesEqualPwise x)

ffcp : FullyFaithful constantPolynomial
ffcp = full , faithful