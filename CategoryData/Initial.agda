{-# OPTIONS --without-K #-}

module CategoryData.Initial where

open import CategoryData.Core
open import CategoryData.SimplePolynomials

arrowFromZero : {p : Polynomial} → Arrow 𝟘 p
arrowFromZero {p} = (λ ()) ⇆ (λ ())