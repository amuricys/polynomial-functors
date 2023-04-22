{-# OPTIONS --sized-types #-}

module Dynamical.Turing where

open import Dynamical.System
open import Data.Nat hiding (_≟_)
open import Data.Fin hiding (_≟_)
open import Data.Integer renaming (_+_ to _+ℤ_ ; _-_ to _-ℤ_)
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Data.Vec
open import Data.Empty
open import Data.Product
open import CategoryData.Everything hiding ( 𝟘 ; 𝟙 )
open import Function
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Bool using (if_then_else_ ; Bool ; true ; false)

------- Processor definitions
ProcessorState : Set
ProcessorState = ℕ 

data ProcessorInput : Set where
  𝟘 𝟙 b : ProcessorInput

data TapeMovement : Set where
  l r : TapeMovement

data ProcessorOutput : Set where
  move : TapeMovement → ProcessorOutput
  write : ProcessorInput → ProcessorOutput
  halt : ProcessorOutput

processorInterface : Polynomial
processorInterface = (MkPoly ProcessorOutput (const ProcessorInput))

turingProgram : Arrow (selfMonomial ProcessorState) processorInterface
turingProgram = exposeState ⇆ updateState
  where exposeState : ProcessorState → ProcessorOutput
        exposeState n = {!  !}
        updateState : ProcessorState → ProcessorInput → ProcessorState
        updateState n toWrite = {!   !}

processor : DynamicalSystem
processor = MkDynamicalSystem ProcessorState processorInterface turingProgram

------- Tape definitions
data TapeState : Set where
  running : (ℤ → ProcessorInput) → TapeState
  halting : (ℤ → ProcessorInput) → TapeState

data TapeOutput : Set where
  instruct : ProcessorInput → TapeOutput
  result : TapeState → TapeOutput

tapeInterface : Polynomial
tapeInterface = MkPoly TapeOutput decide
  where decide : TapeOutput → Set
        decide (instruct x) = ProcessorOutput
        decide (result x) = ⊥

tapeBehavior : Arrow (selfMonomial TapeState) tapeInterface
tapeBehavior = readout ⇆ update
  where readout : TapeState → TapeOutput
        readout (running x) = instruct (x 0ℤ)
        readout (halting x) = result (halting x)
        update : (fromPos : position (selfMonomial TapeState)) → direction tapeInterface (readout fromPos) → direction (selfMonomial TapeState) fromPos
        update (running f) (move l) = running (f ∘ (_+ℤ 1ℤ))
        update (running f) (move r) = running (f ∘ (_-ℤ 1ℤ))
        update (running f) (write x) = running λ x₁ → if ⌊ x₁ ≟ 0ℤ ⌋ then x else f x₁
        update (running x) halt = halting x

tape : DynamicalSystem
tape = MkDynamicalSystem TapeState tapeInterface tapeBehavior

preTuring : DynamicalSystem
preTuring = tape &&& processor

Word : Set
Word = Vec ℤ 32

turingWiringDiagram : Arrow (DynamicalSystem.interface preTuring) (Emitter Word)
turingWiringDiagram = outerOutput ⇆ fillInputs
  where stillRunning = replicate 0ℤ
        outerOutput : TapeOutput × ProcessorOutput → Word
        outerOutput (instruct x₁ , move x) = stillRunning
        outerOutput (result x₁ , move x) = stillRunning
        outerOutput (instruct x₁ , write x) = stillRunning
        outerOutput (result x₁ , write x) = stillRunning
        outerOutput (instruct x , halt) = stillRunning
        outerOutput (result (running x) , halt) = stillRunning
        outerOutput (result (halting x) , halt) = Data.Vec.map (toInt ∘ x) (tabulate (+_ ∘ toℕ))
          where toInt : ProcessorInput → ℤ
                toInt 𝟘 = 0ℤ
                toInt 𝟙 = 1ℤ
                toInt b = 1ℤ +ℤ 1ℤ
        fillInputs : (fromPos : TapeOutput × ProcessorOutput) → ⊤ → direction (DynamicalSystem.interface preTuring) fromPos
        fillInputs (instruct x , proc) tt = proc , x
        fillInputs ( tape , proc ) tt = {!   !}