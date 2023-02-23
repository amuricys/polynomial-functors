{-# OPTIONS --cubical #-}

module AgdaCategories.Functor.Linear where

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
open import AgdaCategories.CubicalPoly
open import Cubical.Proofs
open import Data.Bool

-- Functor sending a set A to the linear polynomial Ay^1 = Ay
linearPolynomial : Functor (Sets Level.zero) Poly
linearPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → ⊤
    ; F₁ = λ f → f ⇄ \ _ _ -> tt
    ; identity = λ i → id ⇄ (λ fromPos x → x)
    ; homomorphism = λ {x y z} {f g} i → (g ∘ f) ⇄ λ fromPos k → k
    ; F-resp-≈ = λ {A B} {f g} x i → let
      cubic : f ≡ g
      cubic = pwiseToExt x
      in
        (cubic i) ⇄ λ fromPos x₁ → x₁
    }
