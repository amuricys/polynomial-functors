{-# OPTIONS --without-K #-}

module Common.CategoryData where

open import Common.Coproduct public
open import Common.Category public
open import Common.Product public
open import Common.Initial public
open import Common.Terminal public
open import Common.SimplePolynomials public
open import Common.Apply public
open import Common.Tensor public
open import Common.Exponential public
open import Common.Composition public

-- Things not belonging elsewhere

enclose : Polynomial → Set
enclose p = Arrow p Y
