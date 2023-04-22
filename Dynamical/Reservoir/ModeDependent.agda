{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Reservoir.ModeDependent where

open import Dynamical.System
open import Data.Product using (_×_; _,_)
open import Data.Sum
open import Data.Unit
open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Float renaming (Float to ℝ; tanh to tanh1) hiding (⌊_⌋)
open import CategoryData.Everything renaming (_*_ to _*p_ ; _+_ to _+p_; Y to Y')
open import Codata.Stream
open import Dynamical.Matrix.Everything as Matrix using (Matrix ; _*ⱽᴹ_ ; _*ᴹⱽ_ ; _*ᴹ_ ; _+ᴹ_ ; _+ⱽ_ ; _ᵀ ; _⁻¹ ; _*ˢᴹ_ ; eye)
open import Dynamical.Reservoir.State
open import Dynamical.Lorenz as Lorenz
open import Data.Vec as Vec using (Vec ; map ; _∷_)
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

data ReadoutOutput (systemDim : ℕ) : Set where
  CD : ReadoutOutput systemDim
  R : Vec ℝ systemDim → ReadoutOutput systemDim

record CollectingDataInput (numNodes systemDim : ℕ) : Set where
  constructor CDI
  field
    resStates : ReservoirState numNodes
    sysOutput : Vec ℝ systemDim

record RunningInput (numNodes : ℕ) : Set where
  constructor RI
  field
    resStates : ReservoirState numNodes

DependentInput : {numNodes systemDim : ℕ} → ReadoutOutput systemDim → Set
DependentInput {numNodes} {systemDim} CD = CollectingDataInput numNodes systemDim
DependentInput {numNodes} (R _) = RunningInput numNodes

reservoir : (numNodes systemDim : ℕ) → DynamicalSystem
reservoir numNodes systemDim = MkDynamicalSystem (ReservoirState numNodes) interface (readout ⇆ update)
  where interface : Polynomial
        interface = MkPoly (ReservoirState numNodes) λ _ → Vec ℝ systemDim × InputWeights numNodes systemDim × ReservoirWeights numNodes
        readout : ReservoirState numNodes → ReservoirState numNodes
        readout = id
        update : ReservoirState numNodes → Vec ℝ systemDim × InputWeights numNodes systemDim × ReservoirWeights numNodes → ReservoirState numNodes
        update (Res nodeStates) (inputSequence , inputWeights , reservoirWeights) = Res (Vec.map tanh1 (reservoirWeights *ᴹⱽ nodeStates +ⱽ inputWeights *ᴹⱽ inputSequence ))

readoutLayer : (numNodes systemDim trainingSteps : ℕ) → DynamicalSystem
readoutLayer numNodes systemDim trainingSteps = MkDynamicalSystem (ReadoutLayerState numNodes systemDim) interface (readout ⇆ update)
  where interface : Polynomial
        interface = MkPoly (ReadoutOutput systemDim) DependentInput
        readout : ReadoutLayerState numNodes systemDim → ReadoutOutput systemDim
        readout (Coll _) = CD -- don't care when training
        readout (Run (Running outputWeights (Res nodeStates))) = R (outputWeights ᵀ *ᴹⱽ nodeStates)
        update : (fromPos : ReadoutLayerState numNodes systemDim) → DependentInput (readout fromPos) → ReadoutLayerState numNodes systemDim
        update (Coll (Collecting counter statesHistory systemHistory outputWeights)) (CDI newNodeStates systemOutput) = 
          if is-≤ counter trainingSteps then keepCollecting else trainThenRun
            where keepCollecting : ReadoutLayerState numNodes systemDim
                  keepCollecting = Coll (Collecting (1 +ℕ counter) (newNodeStates ∷ statesHistory) (systemOutput ∷ systemHistory) outputWeights)
                  trainThenRun : ReadoutLayerState numNodes systemDim
                  trainThenRun = Run (Running trainedOutput initialState)
                    where initialState : ReservoirState numNodes
                          initialState = Res (Vec.replicate 1.0)
                          trainedOutput : OutputWeights numNodes systemDim
                          trainedOutput = (statesHist ᵀ *ᴹ statesHist +ᴹ ridge *ˢᴹ eye) ⁻¹ *ᴹ (statesHist ᵀ *ᴹ systemHist) 
                            where statesHist : Matrix ℝ counter numNodes
                                  statesHist = Matrix.𝕄 (Vec.map ReservoirState.nodeStates statesHistory)
                                  systemHist : Matrix ℝ counter systemDim
                                  systemHist = Matrix.𝕄 systemHistory
                                  ridge = 0.00001
        update (Run (Running outputWeights reservoirState)) (RI resStates) = Run (Running outputWeights resStates)

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
lorenzReservoirWiringDiagram numNodes inputWeights reservoirWeights = outerOutputsFrom ⇆ innerInputsFrom
  where outerOutputsFrom : position
                           (DynamicalSystem.interface (preLorRes numNodes 3 inputWeights reservoirWeights)) →
                           position (Emitter (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ⊎ ⊤))
        outerOutputsFrom ((xnt x , ynt y , znt z) , res , R (predx Vec.∷ predy Vec.∷ predz Vec.∷ Vec.[])) = inj₁ (x , (y , (z , (predx , (predy , predz)))))
        outerOutputsFrom (lor , res , CD) = inj₂ tt
        innerInputsFrom : (fromPos : position (DynamicalSystem.interface (preLorRes numNodes 3 (Matrix.replicate 1.0) (Matrix.replicate 1.0)))) →
                          direction (Emitter (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ⊎ ⊤)) (outerOutputsFrom fromPos) →
                          direction (DynamicalSystem.interface (preLorRes numNodes 3 inputWeights reservoirWeights))
                          fromPos
        innerInputsFrom (lorOutput , resOutput , R readOutput) dir = tt , resInputRunning , readInputRunning
          where resInputRunning : direction (DynamicalSystem.interface (reservoir numNodes 3)) resOutput
                resInputRunning = readOutput , inputWeights , reservoirWeights
                readInputRunning : RunningInput numNodes
                readInputRunning = RI resOutput
        innerInputsFrom (lorOutput , resOutput , CD) dir = tt , resInputTraining , CDI resOutput (outToVec lorOutput)
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

    
lorenzResSeq : 
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  (collState :  CollectingDataState numNodes 3) → Stream (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ⊎ ⊤) _
lorenzResSeq numNodes trainingSteps inputWeights reservoirWeights collState = 
  run (lorenzReservoir numNodes trainingSteps inputWeights reservoirWeights)
      auto
      ((xnt 1.0 , ynt 1.0 , znt 1.0) , (Res (Vec.replicate 0.0)) , Coll collState)

lorenzResList : 
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  (collState :  CollectingDataState numNodes 3) → Vec (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) 5000
lorenzResList numNodes trainingSteps inputWeights reservoirWeights collState = Vec.map (\{(inj₁ x₁) → x₁
                                                                                        ; (inj₂ tt) → 0.0 , 0.0 , 0.0 , 0.0 , 0.0 , 0.0} ) (take 5000 $ lorenzResSeq numNodes trainingSteps inputWeights reservoirWeights collState)
 