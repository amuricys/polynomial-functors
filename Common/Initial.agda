{-# OPTIONS --without-K #-}

module Common.Initial where

open import Common.Category
open import Common.SimplePolynomials

arrowFromZero : {p : Polynomial} → Arrow 𝟘 p
arrowFromZero {p} = (λ ()) ⇄ (λ ())