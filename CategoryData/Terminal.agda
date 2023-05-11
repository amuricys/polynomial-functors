{-# OPTIONS --without-K #-}

module CategoryData.Terminal where

open import CategoryData.Polynomial
open import CategoryData.Lens
open import CategoryData.Chart
open import Data.Unit
open import Data.Empty
open import CategoryData.SimplePolynomials

lensToOne : {p : Polynomial} → Lens p 𝟙
lensToOne = (λ _ → tt) ⇆ λ {_ ()}

chartToOne : {p : Polynomial} → Chart p Y
chartToOne = (λ x → tt) ⇉ λ i x → tt
