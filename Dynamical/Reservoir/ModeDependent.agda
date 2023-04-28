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
open import Data.List using (List ; [] ; reverse)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function
open import Level

import Category.Monad.Reader
open import Category.Monad

is-< : ℕ → ℕ → Bool
is-< a b = ⌊ a Data.Nat.<? b ⌋

tanh : ∀ {m n} → Matrix ℝ m n → Matrix ℝ m n
tanh = Matrix.map tanh1

data ReadoutOutput (numNodes systemDim : ℕ) : Set where
  CD : ReadoutOutput numNodes systemDim
  R : Vec ℝ systemDim → OutputWeights numNodes systemDim → List (ReservoirState numNodes) → List (Vec ℝ systemDim) → ReadoutOutput numNodes systemDim

record CollectingDataInput (numNodes systemDim : ℕ) : Set where
  constructor CDI
  field
    resStates : ReservoirState numNodes
    sysOutput : Vec ℝ systemDim

record RunningInput (numNodes : ℕ) : Set where
  constructor RI
  field
    resStates : ReservoirState numNodes

DependentInput : {numNodes systemDim : ℕ} → ReadoutOutput numNodes systemDim → Set
DependentInput {numNodes} {systemDim} CD = CollectingDataInput numNodes systemDim
DependentInput {numNodes} (R _ _ _ _) = RunningInput numNodes

reservoir : (numNodes systemDim : ℕ) → DynamicalSystem
reservoir numNodes systemDim = MkDynamicalSystem (ReservoirState numNodes) interface (readout ⇆ update)
  where interface : Polynomial
        interface = mkpoly (ReservoirState numNodes) λ _ → Vec ℝ systemDim × InputWeights numNodes systemDim × ReservoirWeights numNodes
        readout : ReservoirState numNodes → ReservoirState numNodes
        readout = id
        update : ReservoirState numNodes → Vec ℝ systemDim × InputWeights numNodes systemDim × ReservoirWeights numNodes → ReservoirState numNodes
        update (Res nodeStates) (inputSequence , inputWeights , reservoirWeights) = Res reservoirActivations
           where inputDynamic : Vec ℝ numNodes
                 inputDynamic = inputWeights *ᴹⱽ inputSequence
                 newReservoirStates : Vec ℝ numNodes
                 newReservoirStates = reservoirWeights *ᴹⱽ nodeStates
                 reservoirActivations : Vec ℝ numNodes
                 reservoirActivations = Vec.map tanh1 (newReservoirStates +ⱽ inputDynamic)

readoutLayer : (numNodes systemDim trainingSteps : ℕ) → DynamicalSystem
readoutLayer numNodes systemDim trainingSteps = MkDynamicalSystem (ReadoutLayerState numNodes systemDim) interface (readout ⇆ update)
  where interface : Polynomial
        interface = mkpoly (ReadoutOutput numNodes systemDim) DependentInput
        readout : ReadoutLayerState numNodes systemDim → ReadoutOutput numNodes systemDim
        readout (Coll _) = CD -- don't care when training
        readout (Run (Running outputWeights (Res nodeStates) statesHist systemHist)) = R (outputWeights ᵀ *ᴹⱽ nodeStates) outputWeights (reverse statesHist) (reverse systemHist)
        update : (fromPos : ReadoutLayerState numNodes systemDim) → DependentInput (readout fromPos) → ReadoutLayerState numNodes systemDim
        update (Coll (Collecting counter statesHistory systemHistory)) (CDI newNodeStates systemOutput) = 
          if is-< counter trainingSteps then keepCollecting else trainThenRun
            where statesHist : Matrix ℝ counter numNodes
                  statesHist = Matrix.𝕄 $ Vec.reverse (Vec.map ReservoirState.nodeStates statesHistory)
                  systemHist : Matrix ℝ counter systemDim
                  systemHist = Matrix.𝕄 $ Vec.reverse systemHistory
                  ridge = 0.01
            
                  keepCollecting : ReadoutLayerState numNodes systemDim
                  keepCollecting = Coll (Collecting (1 +ℕ counter) (newNodeStates ∷ statesHistory) (systemOutput ∷ systemHistory))
                  trainThenRun : ReadoutLayerState numNodes systemDim
                  trainThenRun = Run (Running trainedOutput initialState (Vec.toList statesHistory) (Vec.toList systemHistory))
                    where initialState : ReservoirState numNodes
                          initialState = Res (Vec.replicate 0.0)
                          trainedOutput : OutputWeights numNodes systemDim
                          trainedOutput = (statesHist ᵀ *ᴹ statesHist +ᴹ ridge *ˢᴹ eye)⁻¹ *ᴹ (statesHist ᵀ *ᴹ systemHist) 
          
        update (Run (Running outputWeights reservoirState sth ssh)) (RI resStates) = Run (Running outputWeights resStates sth ssh)

preLorRes : (numNodes trainingSteps : ℕ) → (dt : ℝ) → InputWeights numNodes 3 → ReservoirWeights numNodes → DynamicalSystem
preLorRes numNodes trainingSteps dt inputWeights reservoirWeights = 
  lorenz dt &&& reservoir numNodes 3 &&& readoutLayer numNodes 3 trainingSteps

OuterOutputType : (numNodes : ℕ) →  Set
OuterOutputType numNodes = ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × OutputWeights numNodes 3 × List (ReservoirState numNodes) × List (Vec ℝ 3) ⊎ ⊤

OuterOutput : (numNodes : ℕ) → Polynomial
OuterOutput numNodes = Emitter (OuterOutputType numNodes)


lorenzReservoirWiringDiagram :
  (numNodes : ℕ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) →
   Lens 
    (DynamicalSystem.interface (preLorRes numNodes 3 0.0 inputWeights reservoirWeights))
    (OuterOutput numNodes)
lorenzReservoirWiringDiagram numNodes inputWeights reservoirWeights = outerOutputsFrom ⇆ innerInputsFrom
  where outerOutputsFrom : position
                           (DynamicalSystem.interface (preLorRes numNodes 3 0.0 inputWeights reservoirWeights)) →
                           position (OuterOutput numNodes)
        outerOutputsFrom ((xnt x , ynt y , znt z) , res , R (predx Vec.∷ predy Vec.∷ predz Vec.∷ Vec.[]) ow stateHist sysHis) = inj₁ (x , (y , (z , (predx , (predy , (predz , (ow , (stateHist , sysHis))))))))
        outerOutputsFrom (lor , res , CD) = inj₂ tt
        innerInputsFrom : (fromPos : position (DynamicalSystem.interface (preLorRes numNodes 3 0.0 (Matrix.replicate 1.0) (Matrix.replicate 1.0)))) →
                          direction (OuterOutput numNodes) (outerOutputsFrom fromPos) →
                          direction (DynamicalSystem.interface (preLorRes numNodes 3 0.0 inputWeights reservoirWeights))
                          fromPos
        innerInputsFrom (lorOutput , resOutput , R readOutput ow sh sl) dir = tt , resInputRunning , readInputRunning
          where resInputRunning : direction (DynamicalSystem.interface (reservoir numNodes 3)) resOutput
                resInputRunning = readOutput , inputWeights , reservoirWeights
                readInputRunning : RunningInput numNodes
                readInputRunning = RI resOutput
        innerInputsFrom (lorOutput , resOutput , CD) dir = tt , resInputTraining , CDI resOutput (outToVec lorOutput)
           where resInputTraining : direction (DynamicalSystem.interface (reservoir numNodes 3)) resOutput
                 resInputTraining = Lorenz.outToVec lorOutput , inputWeights , reservoirWeights
                 readInputTraining : ReservoirState numNodes
                 readInputTraining = resOutput
data RestartOrContinue : Set where
  continue : X × Y × Z → RestartOrContinue
  restart : X × Y × Z → RestartOrContinue
restartingLorenz : ℝ → DynamicalSystem
restartingLorenz dt = MkDynamicalSystem (DynamicalSystem.state (lorenz dt) ⊎ X × Y × Z) interface behavior
  where interface : Polynomial
        interface = mkpoly RestartOrContinue λ { (continue _) → ⊤ ; (restart _) → X × Y × Z }
        behavior : Lens (selfMonomial (DynamicalSystem.state (lorenz dt) ⊎ X × Y × Z)) interface
        behavior = readout ⇆ update
           where readout : X × Y × Z ⊎ X × Y × Z  → RestartOrContinue
                 readout (inj₁ x₁) = continue x₁
                 readout (inj₂ lastInputState) = restart lastInputState
                 update : (fromPos : X × Y × Z ⊎ X × Y × Z) → direction interface (readout fromPos) → X × Y × Z ⊎ X × Y × Z
                 update (inj₁ x₁) tt = {!   !}
                 update (inj₂ y₁) inp = {!   !}

lorenzReservoir : 
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (dt : ℝ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  DynamicalSystem
lorenzReservoir numNodes trainingSteps dt inputWeights reservoirWeights = 
  install (preLorRes numNodes trainingSteps dt inputWeights reservoirWeights) 
          (OuterOutput numNodes)
          (lorenzReservoirWiringDiagram numNodes inputWeights reservoirWeights)

    
lorenzResSeq : 
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (lorenzInitialConditions : ℝ × ℝ × ℝ ) →
  (dt : ℝ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  Stream (OuterOutputType numNodes) _
lorenzResSeq numNodes trainingSteps ( ix , iy , iz ) dt inputWeights reservoirWeights = 
  run (lorenzReservoir numNodes trainingSteps dt inputWeights reservoirWeights)
      auto
      ((xnt ix , ynt iy , znt iz) , (Res (Vec.replicate 0.0)) , Coll (Collecting 0 Vec.[] Vec.[]))

lorenzResList : 
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (totalSequenceSteps : ℕ) →
  (lorenzInitialConditions : ℝ × ℝ × ℝ) →
  (dt : ℝ)
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  Vec (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × OutputWeights numNodes 3 × List (ReservoirState numNodes) × List (Vec ℝ 3)) totalSequenceSteps
lorenzResList numNodes trainingSteps totalSequenceSteps lorenzInitialConditions dt inputWeights reservoirWeights = 
    Vec.map discr (take totalSequenceSteps $ lorenzResSeq numNodes trainingSteps lorenzInitialConditions dt inputWeights reservoirWeights)
       where discr : OuterOutputType numNodes → (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ × OutputWeights numNodes 3 × List (ReservoirState numNodes) × List (Vec ℝ 3))
             discr (inj₁ x) = x
             discr (inj₂ tt) = 0.0 , 0.0 , 0.0 , 0.0 , 0.0 , 0.0 , Matrix.𝕄 (Vec.replicate (Vec.replicate 0.0)) , [] , []
  