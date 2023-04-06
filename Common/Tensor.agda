{-# OPTIONS --without-K #-}

module Common.Tensor where

open import Common.Category
open import Common.SimplePolynomials
open import Data.Product

-- Tensor between two polynomials. Parallel product.
-- Pair of position. Each pair of position has one direction for each component.
_⊗_ : Polynomial → Polynomial → Polynomial
MkPoly posA dirA ⊗ MkPoly posB dirB = MkPoly (posA × posB) (λ {(posA , posB) → (dirA posA) × (dirB posB)})

tensorUnit : Polynomial
tensorUnit = Y