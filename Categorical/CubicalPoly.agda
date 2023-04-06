{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.CubicalPoly where

open import Agda.Builtin.Nat hiding (_+_ ; _*_ )
import Agda.Builtin.Nat
open import Level
open import Categories.Category
import Categories.Object.Initial
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
import Cubical.Foundations.Prelude as Cubical
open import Cubical.Data.Sigma.Properties
open import CategoryData.Core
open import Cubical.Proofs
open import Cubical.Foundations.Prelude

open Polynomial
record SetPolynomial : Set₁ where
    constructor MkSetPoly
    field
        poly : Polynomial
        isPosSet : isSet (position poly)
        isDirSet : ∀ {p : position poly} → isSet (direction poly p)

-- Definition of Poly category: integration point between agda-categories and cubical
Poly : Category (Level.suc Level.zero) Level.zero Level.zero
Poly = record
    { Obj = Polynomial
    ; _⇒_ = Arrow
    ; _≈_ = _≡_
    ; id = idArrow
    ; _∘_ = _∘ₚ_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = transitivity }
    ; ∘-resp-≈ = equiv-resp
    }
