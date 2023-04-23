{-# OPTIONS --cubical #-}

module Categorical.Instance.Poly where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Categories.Category
open import CategoryData.Core
open import Cubical.Proofs
open import Cubical.Foundations.Prelude

open Polynomial

-- Definition of Poly category: integration point between agda-categories and cubical
Poly : Category (lsuc lzero) lzero lzero
Poly = record
    { Obj = Polynomial
    ; _⇒_ = Lens
    ; _≈_ = _≡_
    ; id = idLens
    ; _∘_ = _∘ₚ_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = _∙_ }
    ; ∘-resp-≈ = equiv-resp
    }
