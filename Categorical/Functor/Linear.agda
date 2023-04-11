{-# OPTIONS --cubical #-}

module Categorical.Functor.Linear where

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
open import CategoryData.Everything
open import Function
open import Categorical.CubicalPoly
open import Cubical.Proofs
open import Data.Bool

-- Functor sending a set A to the linear polynomial Ay^1 = Ay
linearPolynomial : Functor (Sets Level.zero) Poly
linearPolynomial = record
    { F₀ = λ x → MkPoly x λ _ → ⊤
    ; F₁ = λ f → f ⇄ \ _ _ → tt
    ; identity = λ i → id ⇄ (λ fromPos x → x)
    ; homomorphism = λ {x y z} {f g} i → (g ∘ f) ⇄ λ fromPos k → k
    ; F-resp-≈ = λ {A B} {f g} x i → let
      cubic : f ≡ g
      cubic = pwiseToExt x
      in
        (cubic i) ⇄ λ fromPos x₁ → x₁
    }

full : Full linearPolynomial
full = record 
    { from = record 
        { _⟨$⟩_ = Arrow.mapPosition
        ; cong = positionArrowsEqualPwiseEq } 
    ; right-inverse-of = λ x → refl
    }

faithful : Faithful linearPolynomial
faithful = λ f g x → ctop (positionArrowsEqualPwise x)

ffcp : FullyFaithful linearPolynomial
ffcp = full , faithful