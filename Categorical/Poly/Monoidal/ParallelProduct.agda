{-# OPTIONS --cubical #-}

module Categorical.Poly.Monoidal.ParallelProduct where

open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism hiding (iso)
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs
open import Categories.Category.Monoidal
open import Categorical.Poly.Instance
open import Categories.Functor.Bifunctor
open import Cubical.LensEquality
open import Cubical.Data.Sigma.Properties

open Polynomial
open Lens

-- Monoidal category construction
bifunctor : Bifunctor Poly Poly Poly
bifunctor = record
    { F₀ = λ { (p , q) → p ⊗ q }
    ; F₁ = λ { ((mpf ⇆ mdf) , (mpg ⇆ mdg)) → (λ { (posP , posQ) → mpf posP , mpg posQ }) ⇆ λ { (fromPosP , fromPosQ) (dirFstR , dirSndR) → mdf fromPosP dirFstR , mdg fromPosQ dirSndR } }
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ {(fst₁ , snd₁) → lensesEqual3 (funExt (λ x → {!   !})) -- (funExt λ {(fst , snd) → ≡-× (cong (λ y → mapPosition y fst) fst₁) (cong (λ y → mapPosition y snd) snd₁)}) 
                                                 {!   !} } -- (funExt λ {(fst , snd) → funExt (λ {(fst₁ , snd₁) → {!   !}})})} -- λ { (proofMpEq , proofMdEq) → lens≡∀ (λ i x₁ → {!  !}) {!   !} }
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
open import Categories.Category.Monoidal.Symmetric monoidal
open import Categories.Category.Monoidal.Braided monoidal
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
open import Categories.NaturalTransformation
open Symmetric
open Braided
open NaturalIsomorphism
open NaturalTransformation
open import Data.Product using (_×_)
symmetricMonoidal : Symmetric
η (F⇒G (braiding (braided symmetricMonoidal))) (obj₁ , obj₂) = mp ⇆ md
    where mp : (position obj₁) × (position obj₂) → (position obj₂) × (position obj₁)
          mp (a , b) = b , a
          md : ((pos₁ , pos₂) : (position obj₁ × position obj₂)) → (direction obj₂ pos₂) × (direction obj₁ pos₁) → (direction obj₁ pos₁) × (direction obj₂ pos₂)
          md _ (dir₁ , dir₂) = dir₂ , dir₁
commute (F⇒G (braiding (braided symmetricMonoidal))) = λ f → refl
sym-commute (F⇒G (braiding (braided symmetricMonoidal))) = λ f → refl
η (F⇐G (braiding (braided symmetricMonoidal))) (obj₁ , obj₂) = mp ⇆ md
    where mp : (position obj₂) × (position obj₁) → (position obj₁) × (position obj₂)
          mp (a , b) = b , a
          md : (fromPos : (position obj₂) × (position obj₁)) → (direction obj₁ (snd fromPos)) × (direction obj₂ (fst fromPos)) → (direction obj₂ (fst fromPos)) × (direction obj₁ (snd fromPos))
          md _ (dir₁ , dir₂) = dir₂ , dir₁
commute (F⇐G (braiding (braided symmetricMonoidal))) = λ f → refl
sym-commute (F⇐G (braiding (braided symmetricMonoidal))) = λ f → refl
iso (braiding (braided symmetricMonoidal)) = λ _ → record { isoˡ = refl ; isoʳ = refl }
hexagon₁ (braided symmetricMonoidal) = refl
hexagon₂ (braided symmetricMonoidal) = refl
commutative symmetricMonoidal = refl  