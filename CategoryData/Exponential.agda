{-# OPTIONS --without-K #-}

module CategoryData.Exponential where

open import CategoryData.Polynomial
open import CategoryData.Lens
open import CategoryData.Product
open import CategoryData.Composition
open import CategoryData.SimplePolynomials
open import CategoryData.Coproduct
open import Data.Product


-- Exponential object.
-- Theroem 4.27, page 130 in Poly book.
_^_ : (r : Polynomial) → (q : Polynomial) → Polynomial
r ^ (mkpoly posQ dirQ) = ΠPoly (posQ , λ j → r ◂ (Y + Constant (dirQ j)))
infixl 30 _^_