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

YIsTerminal : IsTerminal Y 
YIsTerminal = record { ! = chartToOne ; !-unique = unique }

terminalY : Terminal
terminalY = record { ⊤ = Y ; ⊤-is-terminal = YIsTerminal }