{-# OPTIONS --cubical  --without-K #-}
module Categorical.Poly.Comonoid.Core where

open import Categories.Category.Core
open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Categorical.Poly.Monoidal.CompositionProduct renaming (assoc to assoc◂)

open import Level

record Comonoid (c : Polynomial) : Set where
  constructor Com
  field
    ε : Lens c Y
    δ : Lens c (c ◂ c)
    assoc : ⟨ idLens {c} ◂ δ ⟩ ∘ₚ δ ≡ subst (λ x → Lens (c ◂ c) {!   !}) (assoc◂ {c} {c} {c}) ⟨ δ ◂ idLens {c} ⟩ ∘ₚ δ
    leftCounit :  ~ᴸ ≡ ⟨ ε ◂ idLens {c} ⟩ ∘ₚ δ
    rightCounit : ~ᴿ ≡ ⟨ idLens {c} ◂ ε ⟩ ∘ₚ δ

comonoidsAreCategories : {emanator : Polynomial} → Comonoid emanator → Category zero zero zero
comonoidsAreCategories {em@(mkpoly pos dir)} (Com ε δ assoc leftCounit rightCounit) = record
  { Obj = pos
  ; _⇒_ = {!   !}
  ; _≈_ = {!   !}
  ; id = {!   !}
  ; _∘_ = {!   !}
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }
  where bookkeeping : {x : pos} → fst (mapPosition δ x) ≡ x
        bookkeeping = {! rightCounit  !} -- use rightCounit
-- categoriesAreComonoids : {emanator : Polynomial} → Category zero zero zero → Comonoid emanator
-- categoriesAreComonoids cat = {!   !}  