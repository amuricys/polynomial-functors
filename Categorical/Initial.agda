{-# OPTIONS --cubical #-}

module Categorical.Initial where

open import CategoryData.Everything
open import Categorical.Instance.Poly
open import Cubical.Proofs
open import Categories.Object.Initial Poly

zeroIsInitial : IsInitial 𝟘 
zeroIsInitial = record { ! = arrowFromZero ; !-unique = arrowFromZeroUnique }

initialZero : Initial
initialZero = record { ⊥ = 𝟘 ; ⊥-is-initial = zeroIsInitial }