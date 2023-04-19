{-# OPTIONS --cubical  --without-K #-}

open import Categories.Category.Core
open import CategoryData.Everything
open import CategoryData.Composition
open import Cubical.Foundations.Prelude

module Categorical.Comonoid.Core where

open import Level

record Comonoid (c : Polynomial) : Set where
  field
    ε : Arrow c Y
    δ : Arrow c (c ◂ c)
    assoc : ⟨ idArrow {c} ◂ δ ⟩ ∘ₚ δ ≡ {!   !} ∘ₚ δ -- some work is needed to make ⟨ δ ◂ idArrow {c} ⟩ typecheck
    leftCounit :  ~ᴸ ≡ ⟨ ε ◂ idArrow {c} ⟩ ∘ₚ δ
    rightCounit : ~ᴿ ≡ ⟨ idArrow {c} ◂ ε ⟩ ∘ₚ δ

comonoidsAreCategories : {emanator : Polynomial} → Comonoid emanator → Category zero zero zero
comonoidsAreCategories {MkPoly pos dir} record { 
  ε = ε ; 
  δ = δ ; 
  assoc = assoc ; 
  leftCounit = leftCounit ; 
  rightCounit = rightCounit 
  } = record
  { Obj = pos
  ; _⇒_ = λ A B → {!   !}
  ; _≈_ = {!   !}
  ; id = λ {A} → {!   !}
  ; _∘_ = {!   !}
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }

categoriesAreComonoids : {emanator : Polynomial} → Category zero zero zero → Comonoid emanator
categoriesAreComonoids cat = {!   !}