{-# OPTIONS --cubical #-}

module Categorical.Coproduct where

open import Categorical.Instance.Poly
open import Categorical.Initial
open import Categories.Object.Coproduct Poly
open import CategoryData.Core
open import Data.Sum
open import Function
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Categories.Category.Monoidal
import Categories.Category.Cocartesian as Cocartesian
open import Cubical.LensEquality
open import CategoryData.Everything

coprod : {A B : Polynomial} → Coproduct A B
coprod {A = A} {B = B} = record
    { A+B = A + B
    ; i₁ = i₁
    ; i₂ = i₂
    ; [_,_] = [_,_]ₚ
    ; inject₁ = refl
    ; inject₂ = refl
    ; unique = unique
    }
    where
        open Lens
        open Polynomial

        helper : {p : Polynomial} {h : Lens (A + B) p} -> [ h ∘ₚ i₁ , h ∘ₚ i₂ ]ₚ ≡ h
        helper {p} {h} = lensesEqual3 (funExt λ {(inj₁ x) → refl
                                               ; (inj₂ y) → refl}) λ {(inj₁ x) y → cong (λ zz → mapDirection h (inj₁ x) zz) ((transportRefl y))
                                                                    ; (inj₂ y₁) y → cong (λ zz → mapDirection h (inj₂ y₁) zz) (transportRefl y)}

        unique : {F : Polynomial} {h : Lens (A + B) F} {f₁ : Lens A F} {f₂ : Lens B F} 
            → (h ∘ₚ i₁) ≡ f₁
            → (h ∘ₚ i₂) ≡ f₂
            → [ f₁ , f₂ ]ₚ ≡ h
        unique p₁ p₂ = (λ i → [ sym p₁ i , sym p₂ i ]ₚ) ∙ helper
