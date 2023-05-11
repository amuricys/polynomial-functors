{-# OPTIONS --cubical #-}

module Categorical.Poly.Terminal where

open import CategoryData.Everything
open import Categorical.Poly.Instance
open import Cubical.Proofs
open import Categories.Object.Terminal Poly

oneIsTerminal : IsTerminal 𝟙 
oneIsTerminal = record { ! = lensToOne ; !-unique = lensToOneUnique }

terminalOne : Terminal
terminalOne = record { ⊤ = 𝟙 ; ⊤-is-terminal = oneIsTerminal }