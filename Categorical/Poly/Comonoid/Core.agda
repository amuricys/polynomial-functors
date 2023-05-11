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
    assoc : ⟨ idLens {c} ◂ δ ⟩ ∘ₚ δ ≡ subst (λ x → Lens (c ◂ c) {! x -- refining with x goes into an infinite loop O_O  !}) (assoc◂ {c} {c} {c}) ⟨ δ ◂ idLens {c} ⟩ ∘ₚ δ
    leftCounit :  ~ᴸ ≡ ⟨ ε ◂ idLens {c} ⟩ ∘ₚ δ
    rightCounit : ~ᴿ ≡ ⟨ idLens {c} ◂ ε ⟩ ∘ₚ δ

open import Relation.Binary.Core
record SmallArrow {emanator : Polynomial} (dom : position emanator) (cod : position emanator) : Set where
  constructor _⟫_

comonoidsAreCategories : {emanator : Polynomial} → Comonoid emanator → Category zero zero zero
comonoidsAreCategories {emanator@(mkpoly pos dir)} (Com ε δ assoc leftCounit rightCounit) = 
  record
    { Obj = pos
    ; _⇒_ = smallArrow
    ; _≈_ = _≡_ 
    ; id = {!   !}
    ; _∘_ = {!   !}
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = {!   !}
    ; identityʳ = {!   !}
    ; identity² = {!   !}
    ; equiv = {!   !}
    ; ∘-resp-≈ = {!   !}
    }
    where smallArrow : Rel pos zero
          smallArrow = λ x x₁ → SmallArrow {emanator} x x₁

categoriesAreComonoids : {emanator : Polynomial} → Category zero zero zero → Comonoid emanator
categoriesAreComonoids cat = {!   !} 