{-# OPTIONS --without-K #-}

module CategoryData.SimplePolynomials where

open import CategoryData.Core
open import Data.Unit
open import Data.Empty

𝟘 : Polynomial
𝟘 = mkpoly ⊥ λ ()

𝟙 : Polynomial
𝟙 = mkpoly ⊤ (λ _ → ⊥)

Y : Polynomial
Y = mkpoly ⊤ (λ _ → ⊤)

-- | p(y) = A*y^B
monomial : (A B : Set) → Polynomial
monomial A B = mkpoly A (λ _ → B)

_y^_ = monomial

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