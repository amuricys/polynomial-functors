{-# OPTIONS --without-K #-}

module CategoryData.Initial where

open import CategoryData.Polynomial
open import CategoryData.Lens
open import CategoryData.Chart
open import CategoryData.SimplePolynomials

lensFromZero : {p : Polynomial} → Lens 𝟘 p
lensFromZero {p} = (λ ()) ⇆ (λ ())

chartFromZero : {p : Polynomial} → Chart 𝟘 p
chartFromZero = (λ ()) ⇉ λ ()
