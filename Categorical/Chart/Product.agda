{-# OPTIONS --cubical #-}

module Categorical.Chart.Product where

open import Categorical.Chart.Instance
open import CategoryData.Everything hiding (π₁ ; π₂ ; ⟨_,_⟩)
open import CategoryData.Chart
open import Categories.Object.Product ChartCat
open import Cubical.Foundations.Prelude
open import Cubical.ChartEquality

π₁ : {p q : Polynomial} → Chart (p ⊗ q) p
π₁ = fst ⇉ λ i → fst

π₂ : {p q : Polynomial} → Chart (p ⊗ q) q
π₂ = snd ⇉ λ i → snd

open Chart
⟨_,_⟩ : {p q r : Polynomial} → Chart p q → Chart p r → Chart p (q ⊗ r)
⟨ f , g ⟩ = (λ p → mapPos f p , mapPos g p) ⇉ λ p x → mapDir f p x , mapDir g p x

prod : {A B : Polynomial} → Product A B
prod {A = A} {B = B} = record
    { A×B = A ⊗ B
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; project₁ = refl
    ; project₂ = refl
    ; unique = unique 
    }
        where
            unique : {p : Polynomial} {h : Chart p (A ⊗ B)} {i : Chart p A} {j : Chart p B} → (π₁ ∘c h) ≡ i → (π₂ ∘c h) ≡ j → ⟨ i , j ⟩ ≡ h
            unique {p} {h = h} pᶠ pᵍ = (λ i → ⟨ sym pᶠ i , sym pᵍ i ⟩) ∙ lemma
                where
                    lemma :  ⟨ (π₁ ∘c h) , (π₂ ∘c h) ⟩ ≡ h
                    lemma = chart≡ refl (substRefl {B = λ (h : position p → position (A ⊗ B)) → (i : position p) → (direction p i) → (direction (A ⊗ B) (h i))} (mapDir ⟨ π₁ ∘c h , π₂ ∘c h ⟩))
