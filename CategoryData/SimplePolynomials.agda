{-# OPTIONS --without-K #-}

module CategoryData.SimplePolynomials where

open import CategoryData.Core
open import Data.Unit
open import Data.Empty

𝟘 : Polynomial
𝟘 = MkPoly ⊥ λ ()

𝟙 : Polynomial
𝟙 = MkPoly ⊤ (λ _ → ⊥)

Y : Polynomial
Y = MkPoly ⊤ (λ _ → ⊤)

-- Constant polynomial: p(y) = A
Constant : (A : Set) → Polynomial
Constant A = MkPoly A (λ _ → ⊥)

monomial : (A B : Set) → Polynomial -- A*Y^B
monomial A B = MkPoly A (λ _ → B)

selfMonomial : Set → Polynomial -- S*Y^S
selfMonomial S = monomial S S

-- | A pure power summand.
purePower : Set → Polynomial
purePower power = MkPoly ⊤ λ _ → power