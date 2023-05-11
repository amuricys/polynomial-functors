
{-# OPTIONS --cubical #-}

module Categorical.Chart.Initial where

open import Categorical.Chart.Instance
open import CategoryData.Chart
open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Categories.Object.Initial ChartCat
open import Cubical.ChartEquality

unique : {p : Polynomial} (f : Chart 𝟘 p) → chartFromZero ≡ f
unique f = chart≡ (funExt λ ()) (funExt λ ())

zeroIsInitial : IsInitial 𝟘 
zeroIsInitial = record { ! = chartFromZero ; !-unique = unique }

initialZero : Initial
initialZero = record { ⊥ = 𝟘 ; ⊥-is-initial = zeroIsInitial }