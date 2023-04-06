{-# OPTIONS --without-K #-}

module Common.Coproduct where

open import Common.Category
open import Common.SimplePolynomials
open import Data.Sum
open import Data.Product
open import Function

-- Coproduct has either of the positions, and its correspoding direction
_+_ : Polynomial → Polynomial → Polynomial
MkPoly posA dirA + MkPoly posB dirB = MkPoly (posA ⊎ posB) [ dirA , dirB ]

coproductUnit : Polynomial
coproductUnit = 𝟘

i₁ : {p q : Polynomial} → Arrow p (p + q)
i₁ = inj₁ ⇄ λ _ → id

i₂ : {p q : Polynomial} → Arrow q (p + q)
i₂ = inj₂ ⇄ λ _ → id

-- The unique factorizer of two arrows
[_,_]ₚ : {p q r : Polynomial} → Arrow p r → Arrow q r → Arrow (p + q) r
[ f ⇄ f♯ , g ⇄ g♯ ]ₚ = [ f , g ] ⇄ [ f♯ , g♯ ]

-- Generalization of the coproduct (_+_).
-- Page 31 in the book.
ΣPoly : Σ[ indexType ∈ Set ] (indexType → Polynomial) → Polynomial
ΣPoly (indexType , generatePoly) = MkPoly pos dir
  where
    -- It is the positions of one of the polynomials
    pos : Set 
    pos = Σ[ index ∈ indexType ] (position (generatePoly index))

    -- It is the direction of the polynomial for the position
    dir : pos → Set
    dir (index , positionAtIndex) = direction (generatePoly index) positionAtIndex