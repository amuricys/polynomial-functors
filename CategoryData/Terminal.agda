{-# OPTIONS --without-K #-}

module CategoryData.Terminal where

open import CategoryData.Core
open import Data.Unit
open import Data.Empty
open import CategoryData.SimplePolynomials

lensToOne : {p : Polynomial} → Lens p 𝟙
lensToOne = (λ _ → tt) ⇆ λ {_ ()}