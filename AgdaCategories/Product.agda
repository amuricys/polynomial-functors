{-# OPTIONS --cubical #-}

module AgdaCategories.Product where

open import AgdaCategories.CubicalPoly
open import Categories.Object.Product Poly
open import Common.CategoryData
open import Agda.Builtin.Sigma
open import Data.Sum
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Data.Product

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

        helper2 : {F : Polynomial} {h : Arrow F (A * B)} → (Arrow.mapDirection ⟨ π₁ ∘p h , π₂ ∘p h ⟩) ≡ Arrow.mapDirection h -- (λ posC → [ (λ z → Arrow.mapDirection h posC (inj₁ z)) , (λ z → Arrow.mapDirection h posC (inj₂ z)) ]) ≡ Arrow.mapDirection h --  {! λ posC → [ (λ z → Arrow.mapDirection h posC (inj₁ z)) , (λ z → Arrow.mapDirection h posC (inj₂ z)) ]) ≡ Arrow.mapDirection h  !} helper2 = {!   !}
        helper2 = λ i fromPos x → {!   !}

        helper : {p  : Polynomial} {h : Arrow p (A * B)} -> ⟨ π₁ ∘p h , π₂ ∘p h ⟩ ≡ h
        helper {h = h} = arrowsEqual refl {! helper2  !} -- fromPos x → {! Arrow.mapDirection h fromPos x  !}
            where
                ye = π₁ ∘p h
                yo = π₂ ∘p h

        unique : {F : Polynomial} {h : Arrow F (A * B)} {f₁ : Arrow F A} {f₂ : Arrow F B} →
            (π₁ ∘p h) ≡ f₁ →
            (π₂ ∘p h) ≡ f₂ → 
            ⟨ f₁ , f₂ ⟩ ≡ h
        unique {F = F} {h = h} p₁ p₂ = transitivity (λ i → ⟨ sym p₁ i , sym p₂ i ⟩) (helper {p = F} {h = h})
