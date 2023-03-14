{-# OPTIONS --sized-types #-}

module Dynamical.Fibonacci where

open import Dynamical.System
open import Agda.Builtin.Nat renaming (_+_ to _+ℕ_)
open import Common.CategoryData
open import Codata.Stream
open import Codata.Thunk
open import Data.List hiding (take; _++_)
open import Data.Vec using (Vec)
import Agda.Builtin.Nat
open import Data.Product

plus : DynamicalSystem
plus = functionToDynamicalSystem (Nat × Nat) Nat (uncurry _+ℕ_)

prefib : DynamicalSystem
prefib = plus &&& delay Nat

fibWiringDiagram : Arrow (DynamicalSystem.interface prefib) (Emitter Nat)
fibWiringDiagram = (λ {(pl , de) → de}) ⇄ (λ {(pl , de) l → (de , pl) , pl })

fibonacci : DynamicalSystem
fibonacci = install prefib (Emitter Nat) fibWiringDiagram

FibSeq : Stream Nat _
FibSeq = run fibonacci auto (1 , 1)

fibList : Vec Nat 50
fibList = take 50 FibSeq
