{-# OPTIONS --cubical #-}

module Categorical.Product where

open import Categorical.Instance.Poly
open import Categories.Object.Product Poly
open import CategoryData.Everything
open import Agda.Builtin.Sigma
open import Data.Sum
open import Cubical.LensEquality
open import Cubical.Foundations.Prelude
open import Data.Product
open import Categories.Category.Monoidal
open import Categorical.Terminal
open import Cubical.LensEquality
import Categories.Category.Cartesian as Cartesian


unique : {p q r : Polynomial} {h : Lens p (q * r)} {f : Lens p q} {g : Lens p r} →
    (π₁ ∘ₚ h) ≡ f →
    (π₂ ∘ₚ h) ≡ g → 
    ⟨ f , g ⟩ ≡ h
unique {p} {q} {r} {h = h} pᶠ pᵍ = (λ i → ⟨ sym pᶠ i , sym pᵍ i ⟩) ∙ lemma
    where
        mapDir≡ : (Lens.mapDirection ⟨ π₁ ∘ₚ h , π₂ ∘ₚ h ⟩) ≡ Lens.mapDirection h
        mapDir≡ = funExt λ posP → funExt λ {(inj₁ _) → refl
                                          ; (inj₂ _) → refl}
        open Polynomial
        lemma : ⟨ π₁ ∘ₚ h , π₂ ∘ₚ h ⟩ ≡ h
        lemma = lens≡ 
            refl 
            ((substRefl 
                {B = λ (h : position p → position (q * r)) → (x : position p) → direction (q * r) (h x) → direction p x}
                (Lens.mapDirection ⟨ π₁ ∘ₚ h , π₂ ∘ₚ h ⟩)
            ) ∙ mapDir≡)

prod : {A B : Polynomial} → Product A B
prod {A = A} {B = B} = record
    { A×B = A * B
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; project₁ = refl
    ; project₂ = refl
    ; unique = unique
    }
