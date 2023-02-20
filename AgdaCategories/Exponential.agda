{-# OPTIONS --cubical #-}

module AgdaCategories.Exponential where

open import AgdaCategories.CubicalPoly
open import Categories.Object.Exponential Poly
open import Common.CategoryData


exp : {A B : Polynomial} -> Exponential A B
exp = record
    { B^A = {!   !}
    ; product = {!   !}
    ; eval = {!   !}
    ; λg = {!   !}
    ; β = {!   !}
    ; λ-unique = {!   !}
    }