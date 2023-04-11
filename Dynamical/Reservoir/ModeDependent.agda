{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Reservoir.ModeDependent where

open import Dynamical.System
open import Data.Product using (_×_; _,_)
open import Data.Sum
open import Data.Unit
open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Float renaming (Float to ℝ; tanh to tanh1) hiding (⌊_⌋)
open import CategoryData.Everything renaming (_*_ to _*p_ ; _+_ to _+p_; Y to Y')
open import Dynamical.Reservoir.Matrix as Matrix using (Matrix ; _*ᴹⱽ_ ; _*ᴹ_ ; _+ⱽ_)
open import Dynamical.Reservoir.State
open import Dynamical.Lorenz as Lorenz
open import Data.Vec as Vec using (Vec ; map)
open import Data.List using (_∷_)
open import Data.Bool using (if_then_else_ ; Bool)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function
open import Level

import Category.Monad.Reader
open import Category.Monad

is-≤ : ℕ → ℕ → Bool
is-≤ a b = ⌊ a Data.Nat.≤? b ⌋

tanh : ∀ {m n} → Matrix ℝ m n → Matrix ℝ m n
tanh = Matrix.map tanh1


activation : ∀ {m n q : ℕ} → Matrix ℝ m n → Matrix ℝ n q → Matrix ℝ m q 
activation nodeStates outputWeights = tanh (nodeStates *ᴹ outputWeights)

reservoir : (numNodes systemDim : ℕ) → DynamicalSystem
reservoir numNodes systemDim = MkDynamicalSystem (ReservoirState numNodes) interface (readout ⇄ update)
  where interface : Polynomial
        interface = MkPoly (ReservoirState numNodes) λ _ → Vec ℝ systemDim × InputWeights numNodes systemDim × ReservoirWeights numNodes
        readout : ReservoirState numNodes → ReservoirState numNodes
        readout = id
        update : ReservoirState numNodes → Vec ℝ systemDim × InputWeights numNodes systemDim × ReservoirWeights numNodes → ReservoirState numNodes
        update (Res nodeStates) (inputSequence , inputWeights , reservoirWeights) = Res (Vec.map tanh1 (reservoirWeights *ᴹⱽ nodeStates +ⱽ inputWeights *ᴹⱽ inputSequence ))

readoutLayer : (numNodes systemDim trainingSteps : ℕ) → DynamicalSystem
readoutLayer numNodes systemDim trainingSteps = MkDynamicalSystem (ReadoutLayerState numNodes systemDim) interface (readout ⇄ update)
  where interface : Polynomial
        interface = MkPoly (Vec ℝ systemDim ⊎ ⊤) λ _ → ReservoirState numNodes
        readout : ReadoutLayerState numNodes systemDim → Vec ℝ systemDim ⊎ ⊤
        readout (Coll (Collecting statesHistory outputWeights counter)) = inj₂ tt -- don't care when training
        readout (Run (Running outputWeights (Res nodeStates))) = inj₁ (outputWeights *ᴹⱽ nodeStates)
        update : ReadoutLayerState numNodes systemDim → ReservoirState numNodes → ReadoutLayerState numNodes systemDim
        update (Coll (Collecting statesHistory outputWeights counter)) (Res newNodeStates) = if is-≤ counter trainingSteps then keepCollecting else trainThenRun
          where keepCollecting : ReadoutLayerState numNodes systemDim
                keepCollecting = Coll (Collecting (Res newNodeStates ∷ statesHistory) outputWeights (counter +ℕ 1))
                trainThenRun : ReadoutLayerState numNodes systemDim
                trainThenRun = Run (Running trainedOutput initialState)
                  where trainedOutput : OutputWeights numNodes systemDim
                        trainedOutput = {! *ᴹ  !}
                        initialState : ReservoirState numNodes
                        initialState = Res (Vec.replicate 1.0)
        update (Run (Running outputWeights reservoirState)) input = Run (Running outputWeights input)

preLorRes : (numNodes trainingSteps : ℕ) → InputWeights numNodes 3 → ReservoirWeights numNodes → DynamicalSystem
preLorRes numNodes trainingSteps inputWeights reservoirWeights = 
  lorenz &&& reservoir numNodes 3 &&& readoutLayer numNodes 3 trainingSteps

lorenzReservoirWiringDiagram :
  (numNodes : ℕ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) →
   Arrow 
    (DynamicalSystem.interface (preLorRes numNodes 3 inputWeights reservoirWeights))
    (Emitter (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ⊎ ⊤))
lorenzReservoirWiringDiagram numNodes inputWeights reservoirWeights = onPos ⇄ onDir
  where onPos : position
                (DynamicalSystem.interface
                (preLorRes numNodes 3 inputWeights reservoirWeights)) →
                position (Emitter (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ⊎ ⊤))
        onPos ((xnt x , ynt y , znt z) , res , inj₁ (predx Vec.∷ predy Vec.∷ predz Vec.∷ Vec.[])) = inj₁ (x , (y , (z , (predx , (predy , predz)))))
        onPos (lor , res , inj₂ stillTraining) = inj₂ stillTraining
        onDir : (fromPos : position (DynamicalSystem.interface (preLorRes numNodes 3 (Matrix.replicate 1.0) (Matrix.replicate 1.0)))) →
                direction (Emitter (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ⊎ ⊤)) (onPos fromPos) →
                direction
                (DynamicalSystem.interface
                (preLorRes numNodes 3 inputWeights reservoirWeights))
                fromPos
        onDir (lorOutput , resOutput , inj₁ readOutput) dir = tt , resInputRunning , readInputRunning
          where resInputRunning : direction (DynamicalSystem.interface (reservoir numNodes 3)) resOutput
                resInputRunning = readOutput , inputWeights , reservoirWeights
                readInputRunning : ReservoirState numNodes
                readInputRunning = resOutput
        onDir (lorOutput , resOutput , inj₂ stillTraining) dir = tt , resInputTraining , readInputTraining
           where resInputTraining : direction (DynamicalSystem.interface (reservoir numNodes 3)) resOutput
                 resInputTraining = Lorenz.outToVec lorOutput , inputWeights , reservoirWeights
                 readInputTraining : ReservoirState numNodes
                 readInputTraining = resOutput
                 

lorenzReservoir : 
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  DynamicalSystem
lorenzReservoir numNodes trainingSteps inputWeights reservoirWeights = 
  install (preLorRes numNodes trainingSteps inputWeights reservoirWeights) 
          (Emitter (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ⊎ ⊤))
          (lorenzReservoirWiringDiagram numNodes inputWeights reservoirWeights)

    