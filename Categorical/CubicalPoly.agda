{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.CubicalPoly where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Categories.Category
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
Poly : Category (lsuc lzero) lzero lzero
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
