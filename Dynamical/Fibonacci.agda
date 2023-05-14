{-# OPTIONS --sized-types #-}

module Dynamical.Fibonacci where

open import Dynamical.System
open import Agda.Builtin.Nat renaming (_+_ to _+ℕ_)
open import CategoryData.Polynomial
open import CategoryData.Lens
open import Codata.Stream
open import Codata.Thunk
open import Data.List hiding (take; _++_)
open import Data.Vec using (Vec)
import Agda.Builtin.Nat
open import Data.Product
open import Function

delay : (A : Set) → DynamicalSystem
delay A = functionToDynamicalSystem A A id

plus : DynamicalSystem
plus = functionToDynamicalSystem (Nat × Nat) Nat (uncurry _+ℕ_)

prefib : DynamicalSystem
prefib = plus &&& delay Nat

fibWiringDiagram : Lens (DynamicalSystem.interface prefib) (emitter Nat)
fibWiringDiagram = (λ {(sumOutput , idOutput) → idOutput}) ⇆ (λ {(sumOutput , idOutput) l → (idOutput , sumOutput) , sumOutput })

fibonacci : DynamicalSystem
fibonacci = install prefib (emitter Nat) fibWiringDiagram

FibSeq : Stream Nat _
FibSeq = run fibonacci auto (1 , 1)

fibList : Vec Nat 50
fibList = take 50 FibSeq
