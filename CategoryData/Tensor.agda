{-# OPTIONS --without-K #-}

module CategoryData.Tensor where

open import CategoryData.Polynomial
open import CategoryData.SimplePolynomials
open import Data.Product

-- Tensor between two polynomials. Parallel product.
-- Pair of position. Each pair of position has one direction for each component.
_⊗_ : Polynomial → Polynomial → Polynomial
mkpoly posA dirA ⊗ mkpoly posB dirB = mkpoly (posA × posB) (λ {(posA , posB) → (dirA posA) × (dirB posB)})
infixl 26 _⊗_

tensorUnit : Polynomial
tensorUnit = Y