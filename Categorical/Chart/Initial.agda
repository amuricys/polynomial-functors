
{-# OPTIONS --cubical #-}

module Categorical.Chart.Initial where

open import Categorical.Chart.ChartCategory
open import CategoryData.Chart.Core
open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Categories.Object.Initial chartCat
open import Cubical.Chart.ChartEquality

chartFromZero : {p : Polynomial} → Chart 𝟘 p
chartFromZero = (λ ()) ⇉ λ ()

unique : {p : Polynomial} (f : Chart 𝟘 p) → chartFromZero ≡ f
unique f = chart≡ (funExt λ ()) (funExt λ ())

zeroIsInitial : IsInitial 𝟘 
zeroIsInitial = record { ! = chartFromZero ; !-unique = unique }

initialZero : Initial
initialZero = record { ⊥ = 𝟘 ; ⊥-is-initial = zeroIsInitial }