{-# OPTIONS --without-K #-}

module Common.Terminal where

open import Common.Category
open import Data.Unit
open import Data.Empty
open import Common.SimplePolynomials

arrowToOne : {p : Polynomial} → Arrow p 𝟙
arrowToOne = (λ _ → tt) ⇄ λ {_ ()}