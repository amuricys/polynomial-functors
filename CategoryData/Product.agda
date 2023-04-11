{-# OPTIONS --without-K #-}

module CategoryData.Product where

open import CategoryData.Core
open import CategoryData.SimplePolynomials
open import Data.Product
open import Data.Sum

-- Product has both positions, but either of the directions
_*_ : Polynomial → Polynomial → Polynomial
MkPoly posA dirA * MkPoly posB dirB = MkPoly (posA × posB) λ { (posA , posB)→ (dirA posA) ⊎ (dirB posB)}
infixl 29 _*_

productUnit : Polynomial
productUnit = 𝟙

π₁ : {p q : Polynomial} → Arrow (p * q) p
π₁ = proj₁ ⇄ λ _ → inj₁

π₂ : {p q : Polynomial} → Arrow (p * q) q
π₂ = proj₂ ⇄ λ _ → inj₂

-- The unique factorizer of two arrows
⟨_,_⟩ : {p q r : Polynomial} → Arrow p q → Arrow p r → Arrow p (q * r)
⟨ f ⇄ f♯ , g ⇄ g♯ ⟩ = < f , g > ⇄ λ posP → [ f♯ posP , g♯ posP ]

-- The parallel arrow from one product to another
⟨_×_⟩ : {A B C D : Polynomial} → (f : Arrow A C) (g : Arrow B D) → Arrow (A * B) (C * D)
⟨_×_⟩ {A} {B} {C} {D} (f ⇄ f♯) (g ⇄ g♯)  = mp ⇄ md
    where mp : position (A * B) → position (C * D)
          mp (a , b) = f a , g b
          md : (fromPos : position (A * B)) → direction (C * D) (mp fromPos) → direction (A * B) fromPos
          md (a , b) (inj₁ x) = inj₁ (f♯ a x)
          md (a , b) (inj₂ y) = inj₂ (g♯ b y)
infixl 30 ⟨_×_⟩


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