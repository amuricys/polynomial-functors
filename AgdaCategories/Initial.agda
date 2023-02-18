{-# OPTIONS --cubical #-}

module AgdaCategories.Initial where

open import Common.CategoryData
open import AgdaCategories.CubicalPoly
open import Cubical.Proofs
open import Categories.Object.Initial Poly

zeroIsInitial : IsInitial Zero 
zeroIsInitial = record { ! = arrowFromZero ; !-unique = arrowFromZeroUnique }

initialZero : Initial
initialZero = record { ⊥ = Zero ; ⊥-is-initial = zeroIsInitial }