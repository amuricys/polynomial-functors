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
------- Common definitions
data Alphabet : Set where
  𝟘 𝟙 𝕓 : Alphabet

data Movement : Set where 
  𝕝 𝕣 : Movement

------- Processor definitions
ProcessorState : Set
ProcessorState = ℕ 

data ProcessorOutput : Set where
  move : Movement → ProcessorOutput
  write : Alphabet → ProcessorOutput
  halt : ProcessorOutput

data ProcessorInput : Set where
  instruction : Alphabet → ProcessorInput

procInputFromOutput : ProcessorOutput → Set
procInputFromOutput (move x) = ProcessorInput
procInputFromOutput (write x) = ProcessorInput
procInputFromOutput halt = ⊤

processorInterface : Polynomial
processorInterface = (mkpoly ProcessorOutput procInputFromOutput)

turingProgram : Lens (selfMonomial ProcessorState) processorInterface
turingProgram = exposeState ⇆ updateState
  where exposeState : ProcessorState → ProcessorOutput
        exposeState (ℕ.suc (ℕ.suc n)) = halt
        exposeState (ℕ.suc zero) = move 𝕣
        exposeState zero = move 𝕝
        updateState : (x : ProcessorState) → procInputFromOutput (exposeState x) → ProcessorState
        updateState zero (instruction x) = {! x  !}
        updateState (ℕ.suc zero) (instruction x) = {!   !}
        updateState (ℕ.suc (ℕ.suc x)) tt = (ℕ.suc (ℕ.suc x))

processor : DynamicalSystem
processor = MkDynamicalSystem ProcessorState processorInterface turingProgram

------- Tape definitions
data TapeInput : Set where
  write : Alphabet → TapeInput
  move : Movement → TapeInput
  halt : TapeInput
  
TapeAt : Set
TapeAt = ℤ → Alphabet

data TapeOutput : Set where
  goOut : Alphabet → TapeOutput
  haltOut : TapeAt → TapeOutput

tapeInputFromOutput : TapeOutput → Set
tapeInputFromOutput (goOut x) = TapeInput
tapeInputFromOutput (haltOut x) = ⊥

tapeInterface : Polynomial
tapeInterface = mkpoly TapeOutput tapeInputFromOutput



data TapeState : Set where
  go : TapeAt → TapeState
  halt : TapeAt → TapeState

tapeBehavior : Lens (selfMonomial TapeState) tapeInterface
tapeBehavior = 
  readout ⇆ update
  where readout : TapeState → TapeOutput
        readout (go tapeAt) = goOut (tapeAt 0ℤ)
        readout (halt tapeAt) = haltOut tapeAt 
        update : (x : TapeState) → (tapeInputFromOutput (readout x)) → TapeState
        update (go tapeAt) (write x) = go (λ tapeIndex → if ⌊ tapeIndex ≟ 0ℤ ⌋ then x else tapeAt tapeIndex)
        update (go tapeAt) (move x) = go (moveTape x tapeAt)
           where moveTape : Movement → TapeAt → TapeAt
                 moveTape 𝕝 f = f ∘ (1ℤ +ℤ_ )
                 moveTape 𝕣 f = f ∘ (1ℤ -ℤ_ )
        update (go tapeAt) halt = halt tapeAt

tape : DynamicalSystem
tape = MkDynamicalSystem TapeState tapeInterface tapeBehavior

preTuring : DynamicalSystem
preTuring = tape &&& processor

open DynamicalSystem
Word : Set
Word = Vec ℤ 256
toInt : Alphabet → ℤ
toInt 𝟘 = 0ℤ
toInt 𝟙 = 1ℤ
toInt 𝕓 = 1ℤ +ℤ 1ℤ
turingWiringDiagram : Lens (interface preTuring) (Emitter (Word ⊎ ⊤))
turingWiringDiagram = outerOutput ⇆ fillInputs
  where outerOutput : TapeOutput × ProcessorOutput → (Word ⊎ ⊤)
        outerOutput (goOut x , procOut) = inj₂ tt
        outerOutput (haltOut x , _) = inj₁ $ Data.Vec.map (toInt ∘ x) (tabulate (+_ ∘ toℕ))
        fillInputs : (fromPos : position (interface preTuring)) →
                     direction (Emitter (Word ⊎ ⊤)) (outerOutput fromPos) → 
                     direction (interface preTuring) fromPos
        fillInputs (goOut tapeInstruction , move procInstruction) tt = move procInstruction , instruction tapeInstruction
        fillInputs (goOut tapeInstruction , write procInstruction) tt = write procInstruction , instruction tapeInstruction
        fillInputs (goOut tapeInstruction , halt) tt = halt , tt
        fillInputs (haltOut x , move x₁) tt = {!   !} , (instruction {!   !})
        fillInputs (haltOut x , write x₁) tt = {!   !}
        fillInputs (haltOut x , halt) tt = {!   !}
        -- fillInputs : (fromPos : TapeOutput × ProcessorOutput) → ⊤ → direction (interface preTuring) fromPos
        -- fillInputs (instruct x , proc) tt = proc , x
        -- fillInputs (result x , x₁) tt = {! x  !}
  