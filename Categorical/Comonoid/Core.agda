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


open import Data.Product

comonoidsAreCategories : {emanator : Polynomial} → Comonoid emanator → Category zero zero zero
comonoidsAreCategories {mkpoly pos dir} record { 
  ε = ε ; 
  δ = δ ; 
  assoc = assoc ; 
  leftCounit = leftCounit ; 
  rightCounit = rightCounit 
  } = record
  { Obj = pos
  ; _⇒_ = λ x x₁ → pos × pos -- experimenting. We might need a deeper relation
  ; _≈_ = _≡_ 
  ; id = λ {A} → A , A
  ; _∘_ = λ { (a , _) (_ , c) → a , c }
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = {!   !} -- yep. we do. this is already impossible. we need to use the data in the comonoid
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }

categoriesAreComonoids : {emanator : Polynomial} → Category zero zero zero → Comonoid emanator
categoriesAreComonoids cat = {!   !}