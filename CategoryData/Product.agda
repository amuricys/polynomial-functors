{-# OPTIONS --without-K #-}

module CategoryData.Product where

open import CategoryData.Core
open import CategoryData.SimplePolynomials
open import Data.Product
open import Data.Sum

-- Product has both positions, but either of the directions
_*_ : Polynomial → Polynomial → Polynomial
MkPoly posA dirA * MkPoly posB dirB = MkPoly (posA × posB) λ { (posA , posB)→ (dirA posA) ⊎ (dirB posB)}

productUnit : Polynomial
productUnit = 𝟙

π₁ : {p q : Polynomial} → Arrow (p * q) p
π₁ = proj₁ ⇄ λ _ → inj₁

π₂ : {p q : Polynomial} → Arrow (p * q) q
π₂ = proj₂ ⇄ λ _ → inj₂

-- The unique factorizer of two arrows
⟨_,_⟩ : {p q r : Polynomial} → Arrow p q → Arrow p r → Arrow p (q * r)
⟨ f ⇄ f♯ , g ⇄ g♯ ⟩ = < f , g > ⇄ λ posP → [ f♯ posP , g♯ posP ]

-- Generalization of the product
ΠPoly : Σ[ indexType ∈ Set ] (indexType → Polynomial) → Polynomial
ΠPoly (indexType , generatePoly) = MkPoly pos dir
  where
    -- Embedding all polynomial positions into one position
    pos : Set
    pos = (index : indexType) → position (generatePoly index)

    -- Direction is exactly one of the polynomials directions
    dir : pos → Set
    dir pos = Σ[ index ∈ indexType ] direction (generatePoly index) (pos index)