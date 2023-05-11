{-# OPTIONS --cubical #-}

module Categorical.Chart.Terminal where

open import Categorical.Chart.Instance
open import CategoryData.Chart
open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Categories.Object.Terminal ChartCat
open import Cubical.ChartEquality
open import Data.Unit

unique : {p : Polynomial} (f : Chart p Y) → chartToOne ≡ f
unique f = chart≡ refl refl

oneIsTerminal : IsTerminal Y 
oneIsTerminal = record { ! = chartToOne ; !-unique = unique }

terminalOne : Terminal
terminalOne = record { ⊤ = Y ; ⊤-is-terminal = oneIsTerminal }