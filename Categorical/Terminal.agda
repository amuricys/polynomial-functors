{-# OPTIONS --cubical #-}

module Categorical.Terminal where

open import Common.CategoryData
open import Categorical.CubicalPoly
open import Cubical.Proofs
open import Categories.Object.Terminal Poly

oneIsTerminal : IsTerminal One 
oneIsTerminal = record { ! = arrowToOne ; !-unique = arrowToOneUnique }

terminalOne : Terminal
terminalOne = record { ⊤ = One ; ⊤-is-terminal = oneIsTerminal }