{-# OPTIONS --cubical #-}

module Categorical.Chart.Instance where

open import Categories.Category
open import Level
open import CategoryData.Chart
open import CategoryData.Everything
open import Cubical.Foundations.Prelude

ChartCat : Category (ℓ-suc ℓ-zero) ℓ-zero ℓ-zero
ChartCat = record
    { Obj = Polynomial
    ; _⇒_ = Chart
    ; _≈_ = _≡_
    ; id = idChart
    ; _∘_ = _∘c_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = _∙_ }
    ; ∘-resp-≈ = λ p q i → (p i) ∘c (q i)
    }
