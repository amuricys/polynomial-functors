{-# OPTIONS --without-K #-}

module Common.Composition where

open import Common.Category
open import Common.SimplePolynomials
open import Data.Product
open import Agda.Builtin.Nat

-- Composition of polynomials (composition of polynomial functors, which happen to be new polynomial functor!).
-- Proposition 5.2, page 158. Note: not same definition used.
_◂_ : Polynomial → Polynomial → Polynomial
p ◂ q = MkPoly pos dir
  where
    module p = Polynomial p
    module q = Polynomial q

    pos : Set
    pos = (Σ[ i ∈ p.position ] (p.direction i → q.position))

    dir : pos → Set
    dir (i , j) = Σ[ a ∈ p.direction i ] q.direction (j a)

compositionUnit : Polynomial
compositionUnit = 𝕐

compositePower : Polynomial → Nat → Polynomial
compositePower p zero = compositionUnit
compositePower p (suc n) = p ◂ (compositePower p n) 