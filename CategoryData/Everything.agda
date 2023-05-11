{-# OPTIONS --without-K #-}

module CategoryData.Everything where

open import CategoryData.Coproduct public
open import CategoryData.Polynomial public
open import CategoryData.Lens public
open import CategoryData.Product public
open import CategoryData.Initial public
open import CategoryData.Terminal public
open import CategoryData.SimplePolynomials public
open import CategoryData.Apply public
open import CategoryData.Tensor public
open import CategoryData.Exponential public
open import CategoryData.Composition public

-- Things not belonging elsewhere

enclose : Polynomial → Set
enclose p = Lens p Y
