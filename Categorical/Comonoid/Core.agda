{-# OPTIONS --cubical  --without-K #-}

open import Categories.Category.Core
open import CategoryData.Everything
open import CategoryData.Composition
open import Cubical.Foundations.Prelude

module Categorical.Comonoid.Core where

open import Level

record Comonoid (c : Polynomial) : Set where
  field
    ε : Lens c Y
    δ : Lens c (c ◂ c)
    assoc : ⟨ idLens {c} ◂ δ ⟩ ∘ₚ δ ≡ {!   !} ∘ₚ δ -- some work is needed to make ⟨ δ ◂ idLens {c} ⟩ typecheck
    leftCounit :  ~ᴸ ≡ ⟨ ε ◂ idLens {c} ⟩ ∘ₚ δ
    rightCounit : ~ᴿ ≡ ⟨ idLens {c} ◂ ε ⟩ ∘ₚ δ

open import Relation.Binary.Core
record SmallArrow {emanator : Polynomial} (dom : position emanator) (cod : position emanator) : Set where
  constructor _⟫_
  

open import Data.Product



comonoidsAreCategories : {emanator : Polynomial} → Comonoid emanator → Category zero zero zero
comonoidsAreCategories {emanator@(mkpoly pos dir)} record { 
  ε = ε ; 
  δ = δ ; 
  assoc = assoc ; 
  leftCounit = leftCounit ; 
  rightCounit = rightCounit 
  } = record
  { Obj = pos
  ; _⇒_ = smallArrow -- experimenting. We might need a deeper relation
  ; _≈_ = _≡_ 
  ; id = {!   !}
  ; _∘_ = {!   !}
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = {!   !} -- yep. we do. this is already impossible. we need to use the data in the comonoid
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }
  where smallArrow : Rel pos zero
        smallArrow = λ x x₁ → SmallArrow {emanator} x x₁

categoriesAreComonoids : {emanator : Polynomial} → Category zero zero zero → Comonoid emanator
categoriesAreComonoids cat = {!   !}