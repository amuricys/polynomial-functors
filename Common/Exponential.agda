{-# OPTIONS --without-K #-}

module Common.Exponential where

open import Common.Category
open import Common.Product
open import Common.Composition
open import Common.SimplePolynomials
open import Common.Coproduct
open import Data.Product


-- Exponential object.
-- Theroem 4.27, page 130 in Poly book.
_^_ : (r : Polynomial) → (q : Polynomial) → Polynomial
r ^ (MkPoly posQ dirQ) = ΠPoly (posQ , λ j → r ◂ (𝕐 + Constant (dirQ j)))