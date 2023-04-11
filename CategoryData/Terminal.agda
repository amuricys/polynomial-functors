{-# OPTIONS --without-K #-}

module CategoryData.Terminal where

open import CategoryData.Core
open import Data.Unit
open import Data.Empty
open import CategoryData.SimplePolynomials

arrowToOne : {p : Polynomial} → Arrow p 𝟙
arrowToOne = (λ _ → tt) ⇄ λ {_ ()}