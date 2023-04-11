{-# OPTIONS --without-K #-}

module CategoryData.Composition where

open import CategoryData.Core
open import CategoryData.SimplePolynomials
open import Data.Product
open import Agda.Builtin.Nat

-- Composition of polynomials (remember, polynomials are ENDOfunctors so they compose 
-- to give a new polynomial functor!).
-- Proposition 5.2, page 158. Note: not same definition used. We here treat positions
-- as inhabitants of the same set, which makes a lot of proofs easier down the line.
_◂_ : Polynomial → Polynomial → Polynomial
p ◂ q = MkPoly pos dir
  where
    module p = Polynomial p
    module q = Polynomial q

    pos : Set
    pos = (Σ[ i ∈ p.position ] (p.direction i → q.position))

    dir : pos → Set
    dir (i , j) = Σ[ a ∈ p.direction i ] q.direction (j a)
infixl 27 _◂_

compositionUnit : Polynomial
compositionUnit = Y

compositePower : Polynomial → Nat → Polynomial
compositePower p zero = compositionUnit
compositePower p (suc n) = p ◂ (compositePower p n) 