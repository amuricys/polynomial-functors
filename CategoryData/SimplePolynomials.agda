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

-- | p(y) = A*y^B
monomial : (A B : Set) → Polynomial
monomial A B = MkPoly A (λ _ → B)

-- | p(y) = A
Constant : (A : Set) → Polynomial
Constant A = monomial A ⊥

-- | p(y) = S*y^S
selfMonomial : Set → Polynomial
selfMonomial S = monomial S S

-- | p(y) = y^S
purePower : Set → Polynomial
purePower power = monomial ⊤ power

-- | p(y) = A*y
linear : (A : Set) → Polynomial
linear A = monomial A ⊤ 