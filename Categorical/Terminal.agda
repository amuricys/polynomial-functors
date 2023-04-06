{-# OPTIONS --cubical #-}

module Categorical.Terminal where

open import Common.CategoryData
open import Categorical.CubicalPoly
open import Cubical.Proofs
open import Categories.Object.Terminal Poly

oneIsTerminal : IsTerminal 𝟙 
oneIsTerminal = record { ! = arrowToOne ; !-unique = arrowToOneUnique }

terminalOne : Terminal
terminalOne = record { ⊤ = 𝟙 ; ⊤-is-terminal = oneIsTerminal }