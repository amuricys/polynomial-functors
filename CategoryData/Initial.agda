{-# OPTIONS --without-K #-}

module CategoryData.Initial where

open import CategoryData.Core
open import CategoryData.SimplePolynomials

lensFromZero : {p : Polynomial} → Lens 𝟘 p
lensFromZero {p} = (λ ()) ⇆ (λ ())