{-# OPTIONS --cubical #-}

module Categorical.Monoidal.ParallelProduct where

open import CategoryData.Core
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs
open import Categories.Category.Monoidal
open import Categorical.Instance.Poly
open import Categories.Functor.Bifunctor
open import Cubical.ArrowEquals
open import Cubical.Data.Sigma.Properties

open Polynomial

-- Monoidal category construction
bifunctor : Bifunctor Poly Poly Poly
bifunctor = record
    { F₀ = λ { (p , q) → p ⊗ q }
    ; F₁ = λ { ((mpf ⇆ mdf) , (mpg ⇆ mdg)) → (λ { (posP , posQ) → mpf posP , mpg posQ }) ⇆ λ { (fromPosP , fromPosQ) (dirFstR , dirSndR) → mdf fromPosP dirFstR , mdg fromPosQ dirSndR } }
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ {(fst₁ , snd₁) → arrow≡ (funExt λ {(fst , snd) → ≡-× (cong (λ y → Arrow.mapPosition y fst) fst₁) (cong (λ y → Arrow.mapPosition y snd) snd₁)}) (funExt λ {(fst , snd) → funExt (λ {(fst₁ , snd₁) → {!   !}})})} -- λ { (proofMpEq , proofMdEq) → arrow≡∀ (λ i x₁ → {!  !}) {!   !} }
    }

monoidal : Monoidal Poly
monoidal = record
    { ⊗ = bifunctor
    ; unit = Y
    ; unitorˡ = record { 
        from = snd ⇆ λ { _ → tt ,_ } ; 
        to = (tt ,_ ) ⇆ λ _ → snd ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; unitorʳ = record { 
        from = fst ⇆ λ _ → _, tt ; 
        to = (_, tt) ⇆ λ _ → fst ; 
        iso = record { isoˡ = refl ; isoʳ = refl }
        }
    ; associator = record { 
        from = (λ { ((fst₁ , snd₂) , snd₁) → fst₁ , snd₂ , snd₁ }) ⇆ λ { ((fst₁ , snd₂) , snd₁) x → (fst x , fst (snd x)) , snd (snd x) } ; 
        to = (λ { (fst₁ , fst₂ , snd₁) → (fst₁ , fst₂) , snd₁ }) ⇆ λ { (fst₁ , snd₁) ((fst₂ , snd₃) , snd₂) → fst₂ , snd₃ , snd₂ } ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; unitorˡ-commute-from = refl
    ; unitorˡ-commute-to = refl
    ; unitorʳ-commute-from = refl
    ; unitorʳ-commute-to = refl
    ; assoc-commute-from = refl
    ; assoc-commute-to = refl
    ; triangle = refl
    ; pentagon = refl
    }