{-# OPTIONS --cubical #-}

module Categorical.Chart.Terminal where

open import Categorical.Chart.ChartCategory
open import CategoryData.Chart.Core
open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Categories.Object.Terminal chartCat
open import Cubical.Chart.ChartEquality
open import Data.Unit

chartToOne : {p : Polynomial} → Chart p Y
chartToOne = (λ x → tt) ⇉ λ i x → tt

unique : {p : Polynomial} (f : Chart p Y) → chartToOne ≡ f
unique f = chart≡ refl refl

oneIsTerminal : IsTerminal Y 
oneIsTerminal = record { ! = chartToOne ; !-unique = unique }

terminalOne : Terminal
terminalOne = record { ⊤ = Y ; ⊤-is-terminal = oneIsTerminal }