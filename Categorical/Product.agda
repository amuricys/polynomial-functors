{-# OPTIONS --cubical #-}

module Categorical.Product where

open import Categorical.CubicalPoly
open import Categories.Object.Product Poly
open import Common.CategoryData
open import Agda.Builtin.Sigma
open import Data.Sum
open import Cubical.Proofs
open import Cubical.ArrowEquals
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Data.Product
open import Categories.Category.Monoidal
open import Categorical.Terminal
import Categories.Category.Cartesian as Cartesian

prod : {A B : Polynomial} -> Product A B
prod {A = A} {B = B} = record
    { A×B = A * B
    ; π₁ = π₁  --fst ⇄ λ _ → inj₁
    ; π₂ = π₂ -- snd ⇄ λ _ → inj₂
    ; ⟨_,_⟩ = ⟨_,_⟩ -- λ {(f ⇄ f♯) (g ⇄ g♯) → < f , g > ⇄ λ posC → [ f♯ posC , g♯ posC ]}
    ; project₁ = refl
    ; project₂ = refl
    ; unique = unique
    }

    where
    
        π₁ = fst ⇄ λ _ → inj₁
        π₂ = snd ⇄ λ _ → inj₂

        ⟨_,_⟩ : {C : Polynomial} → Arrow C A → Arrow C B → Arrow C (A * B)
        ⟨_,_⟩ = λ {(f ⇄ f♯) (g ⇄ g♯) → < f , g > ⇄ λ posC → [ f♯ posC , g♯ posC ]}

        base : {F : Polynomial} {h : Arrow F (A * B)} → (Arrow.mapDirection ⟨ π₁ ∘p h , π₂ ∘p h ⟩) ≡ Arrow.mapDirection h
        base = funExt λ x → funExt λ {(inj₁ x) → refl
                                       ; (inj₂ y) → refl}

        lemma : {p : Polynomial} {h : Arrow p (A * B)} -> ⟨ π₁ ∘p h , π₂ ∘p h ⟩ ≡ h
        lemma {p} {h} = arrow≡ refl (substRefl 
                {B = (λ (h : Polynomial.position p → Polynomial.position (A * B)) → (x : Polynomial.position p) → Polynomial.direction (A * B) (h x) → Polynomial.direction p x)}
                (Arrow.mapDirection ⟨ π₁ ∘p h , π₂ ∘p h ⟩) ∙ base)


        unique : {F : Polynomial} {h : Arrow F (A * B)} {f₁ : Arrow F A} {f₂ : Arrow F B} →
            (π₁ ∘p h) ≡ f₁ →
            (π₂ ∘p h) ≡ f₂ → 
            ⟨ f₁ , f₂ ⟩ ≡ h
        unique {F = F} {h = h} p₁ p₂ = transitivity (λ i → ⟨ sym p₁ i , sym p₂ i ⟩) (lemma {p = F} {h = h})

binaryProducts : Cartesian.BinaryProducts Poly
binaryProducts = record { product = prod }

cartesian : Cartesian.Cartesian Poly
cartesian = record { terminal = terminalOne ; products = binaryProducts }

productMonoidal : Monoidal Poly
productMonoidal = Cartesian.CartesianMonoidal.monoidal Poly cartesian
