{-# OPTIONS --cubical #-}

module Categorical.Product where

open import Categorical.CubicalPoly
open import Categories.Object.Product Poly
open import Common.CategoryData
open import Agda.Builtin.Sigma
open import Data.Sum
open import Cubical.ArrowEquals
open import Cubical.Foundations.Prelude
open import Data.Product
open import Categories.Category.Monoidal
open import Categorical.Terminal
open import Cubical.ArrowEquals
import Categories.Category.Cartesian as Cartesian

π₁ : {p q : Polynomial} → Arrow (p * q) p
π₁ = fst ⇄ λ _ → inj₁

π₂ : {p q : Polynomial} → Arrow (p * q) q
π₂ = snd ⇄ λ _ → inj₂

⟨_,_⟩ : {p q r : Polynomial} → Arrow p q → Arrow p r → Arrow p (q * r)
⟨ f ⇄ f♯ , g ⇄ g♯ ⟩ = < f , g > ⇄ λ posP → [ f♯ posP , g♯ posP ]

unique : {p q r : Polynomial} {h : Arrow p (q * r)} {f : Arrow p q} {g : Arrow p r} →
    (π₁ ∘p h) ≡ f →
    (π₂ ∘p h) ≡ g → 
    ⟨ f , g ⟩ ≡ h
unique {p} {q} {r} {h = h} pᶠ pᵍ = (λ i → ⟨ sym pᶠ i , sym pᵍ i ⟩) ∙ lemma
    where
        mapDir≡ : (Arrow.mapDirection ⟨ π₁ ∘p h , π₂ ∘p h ⟩) ≡ Arrow.mapDirection h
        mapDir≡ = funExt λ posP → funExt λ {(inj₁ _) → refl
                                          ; (inj₂ _) → refl}
        open Polynomial
        lemma : ⟨ π₁ ∘p h , π₂ ∘p h ⟩ ≡ h
        lemma = arrow≡ refl ((substRefl 
         {B = (λ (h : position p → position (q * r)) → (x : position p) → direction (q * r) (h x) → direction p x)}
         (Arrow.mapDirection ⟨ π₁ ∘p h , π₂ ∘p h ⟩)) ∙ mapDir≡)

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

binaryProducts : Cartesian.BinaryProducts Poly
binaryProducts = record { product = prod }

cartesian : Cartesian.Cartesian Poly
cartesian = record { terminal = terminalOne ; products = binaryProducts }

productMonoidal : Monoidal Poly
productMonoidal = Cartesian.CartesianMonoidal.monoidal Poly cartesian
