{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Reservoir.ModeDependent where

open import Dynamical.System
open import Data.Product using (_×_; _,_)
open import Data.Sum
open import Data.Unit
open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Float renaming (Float to ℝ; tanh to tanh1; show to showf) hiding (⌊_⌋)
open import CategoryData.Everything renaming (_*_ to _*p_ ; _+_ to _+p_; Y to Y')
open import Codata.Stream using (Stream ; take ; drop)
open import Dynamical.Matrix.Everything as Matrix using (Matrix ; _*ⱽᴹ_ ; _*ᴹⱽ_ ; _*ᴹ_ ; _+ᴹ_ ; _+ⱽ_ ; _ᵀ ; _⁻¹ ; _*ˢᴹ_ ; eye)
open import Dynamical.Reservoir.State
open import Dynamical.Lorenz as Lorenz
open import Data.Vec as Vec using (Vec ; map ; _∷_)
open import Data.Bool using (if_then_else_ ; Bool)
open import Data.List using (List ; [] ; reverse)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Function
open import Level
open DynamicalSystem renaming (interface to interfaceₚ)
open ReservoirState
open import Data.Bool

import Category.Monad.Reader
open import Category.Monad

is-< : ℕ → ℕ → Bool
is-< a b = ⌊ a Data.Nat.<? b ⌋

is-≡ : ℕ → ℕ → Bool
is-≡ a b = ⌊ a Data.Nat.≟ b ⌋

tanh : ∀ {m n} → Matrix ℝ m n → Matrix ℝ m n
tanh = Matrix.map tanh1

open import Data.String
postulate trace : ∀ {A : Set} → String → A → A
{-# FOREIGN GHC
  import Debug.Trace
  import Data.Text

  myTrace :: Text -> a -> a
  myTrace str a = trace (unpack str) a
#-}
{-# COMPILE GHC trace = \_ -> myTrace #-}

data ReadoutOutput (numNodes systemDim : ℕ) : Set where
  CD : ReadoutOutput numNodes systemDim
  R : Vec ℝ systemDim → OutputWeights numNodes systemDim → ReadoutOutput numNodes systemDim

record CollectingDataInput (numNodes systemDim : ℕ) : Set where
  constructor CDI
  field
    resStates : ReservoirState numNodes
    sysOutput : Vec ℝ systemDim

RunningInput : (numNodes : ℕ) → Set
RunningInput = ReservoirState

DependentInput : {numNodes systemDim : ℕ} → ReadoutOutput numNodes systemDim → Set
DependentInput {numNodes} {systemDim} CD = CollectingDataInput numNodes systemDim
DependentInput {numNodes} (R _ _ ) = RunningInput numNodes

reservoir : (numNodes systemDim : ℕ) → DynamicalSystem
reservoir numNodes systemDim = mkdyn (ReservoirState numNodes) interface (readout ⇆ update)
  where interface : Polynomial
        interface = mkpoly (ReservoirState numNodes) λ _ → Vec ℝ systemDim × InputWeights numNodes systemDim × ReservoirWeights numNodes × Bool
        readout : ReservoirState numNodes → ReservoirState numNodes
        readout = id
        update : ReservoirState numNodes → Vec ℝ systemDim × InputWeights numNodes systemDim × ReservoirWeights numNodes × Bool → ReservoirState numNodes
        update (Res nodes) (inputSequence , inputWeights , _ , true) =
          Res reservoirActivations
          where reservoirActivations = (Vec.replicate 0.0)
        update (Res nodeStates) (inputSequence , inputWeights , reservoirWeights , _) =
          Res reservoirActivations
          where inputDynamic : Vec ℝ numNodes
                inputDynamic = inputWeights *ᴹⱽ inputSequence
                newReservoirStates : Vec ℝ numNodes
                newReservoirStates = reservoirWeights *ᴹⱽ nodeStates
                reservoirActivations : Vec ℝ numNodes
                reservoirActivations = Vec.map tanh1 (newReservoirStates +ⱽ inputDynamic)

readoutLayer : (numNodes systemDim trainingSteps : ℕ) → DynamicalSystem
readoutLayer numNodes systemDim trainingSteps = mkdyn (ReadoutLayerState numNodes systemDim) interface (readout ⇆ update)
  where interface : Polynomial
        interface = mkpoly (ReadoutOutput numNodes systemDim) DependentInput
        readout : ReadoutLayerState numNodes systemDim → ReadoutOutput numNodes systemDim
        readout (Coll _) = CD -- don't care when training
        readout (Run (Running outputWeights (Res lastSeenNodeStates))) = R (outputWeights ᵀ *ᴹⱽ lastSeenNodeStates) outputWeights
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
                  trainThenRun = Run (Running trainedOutputWeights initialState)
                    where initialState : ReservoirState numNodes
                          initialState = Res (Vec.replicate 0.0)
                          trainedOutputWeights : OutputWeights numNodes systemDim
                          trainedOutputWeights = (statesHist ᵀ *ᴹ statesHist +ᴹ ridge *ˢᴹ eye {n = numNodes})⁻¹ *ᴹ (statesHist ᵀ *ᴹ systemHist)
        update (Run (Running outputWeights (Res lastSeenNodeStates))) (Res nodeStateFromReservoir) = 
          Run (Running outputWeights (Res nodeStateFromReservoir))
          -- where str =
          --             "Readout's conception of node states (what you'd get from a readout): \n"
          --             ++ Matrix.showVec (outputWeights ᵀ *ᴹⱽ lastSeenNodeStates)
          --             -- ++ "\nResult of multiplying owᵀ = \n"
          --             -- ++ Matrix.showMatrix (outputWeights ᵀ)
          --             -- ++ "with its current nodeStates = \n"
          --             -- ++ Matrix.showVec lastSeenNodeStates

data TouchCtrl : Set where
  touching : Bool → TouchCtrl
  going : TouchCtrl
ctr : {numNodes systemDim : ℕ} → ℕ → DynamicalSystem
ctr {nN} {sd} touchSteps = mkdyn ℕ (mkpoly TouchCtrl (λ x₁ → ReadoutOutput nN sd)) (crossThreshold ⇆ countUp)
  where crossThreshold : ℕ → TouchCtrl
        crossThreshold st = 
          if is-< st touchSteps then 
            touching (is-≡ st 0) else 
            going
        countUp : ℕ → ReadoutOutput nN sd → ℕ
        countUp st CD = st
        countUp st (R _ _) = st +ℕ 1



preLorRes : (numNodes trainingSteps touchSteps : ℕ) → (dt : ℝ) → InputWeights numNodes 3 → ReservoirWeights numNodes → DynamicalSystem
preLorRes numNodes trainingSteps touchSteps dt inputWeights reservoirWeights = 
  -- Training system
  lorenz dt &&& 
  -- Test system
  canResetLorenz dt &&&
  -- Counter controlling wiring pattern
  ctr {numNodes} {3} touchSteps  &&&
  -- Reservoir of dynamics
  reservoir numNodes 3 &&&
  -- Readout layer
  readoutLayer numNodes 3 trainingSteps
OuterOutputType : (numNodes : ℕ) →  Set
OuterOutputType numNodes = ℝ × ℝ × ℝ × ℝ × ℝ × ℝ ⊎ ⊤

OuterOutput : (numNodes : ℕ) → Polynomial
OuterOutput numNodes = emitter (OuterOutputType numNodes)

lorenzReservoirWiringDiagram :
  (numNodes : ℕ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) →
   Lens 
    (interfaceₚ (preLorRes numNodes 3 3 0.0 inputWeights reservoirWeights))
    (OuterOutput numNodes)
lorenzReservoirWiringDiagram numNodes inputWeights reservoirWeights = outerOutputsFrom ⇆ innerInputsFrom
  where outerOutputsFrom : position
                           (interfaceₚ (preLorRes numNodes 3 3 0.0 inputWeights reservoirWeights)) →
                           position (OuterOutput numNodes)
        outerOutputsFrom (_ , _ , _ , _ , CD) = inj₂ tt
        outerOutputsFrom (_ , (xnt x , ynt y , znt z) , touching _ , _ , R (predx ∷ predy ∷ predz ∷ Vec.[]) ow) = inj₁ (x , y , z , predx , predy , predz)
        outerOutputsFrom ((xnt x , ynt y , znt z) , _ , going , res , R (predx ∷ predy ∷ predz ∷ Vec.[]) ow) = inj₁ (x , y , z , predx , predy , predz)
        innerInputsFrom : (fromPos : (X × Y × Z) × (X × Y × Z) × TouchCtrl × (ReservoirState numNodes) × (ReadoutOutput numNodes 3)) → 
                          ⊤ → 
                          (direction (interfaceₚ (preLorRes numNodes 3 3 0.0 inputWeights reservoirWeights)) fromPos)
                          
        innerInputsFrom (_ , lorTestOutput , touching true , resOutput , ro@(R readOutput ow )) dir = tt , inj₂ ((xnt 4.0 , ynt 4.0 , znt 4.0)) , ro , resInputTouching , readInputTouching
          where resInputTouching : direction (interfaceₚ (reservoir numNodes 3)) resOutput
                resInputTouching = Lorenz.outToVec lorTestOutput , inputWeights , reservoirWeights , true
                readInputTouching : RunningInput numNodes
                readInputTouching = resOutput
        innerInputsFrom (_ , lorTestOutput , touching false , resOutput , ro@(R readOutput ow )) dir = tt , inj₁ tt , ro , resInputTouching , readInputTouching
          where resInputTouching : direction (interfaceₚ (reservoir numNodes 3)) resOutput
                resInputTouching = Lorenz.outToVec lorTestOutput , inputWeights , reservoirWeights , false
                readInputTouching : RunningInput numNodes
                readInputTouching = resOutput
        innerInputsFrom (lorTrainingOutput , _ , going , resOutput , ro@(R readOutput ow)) dir = -- trace str $ 
          tt , inj₁ tt , ro , resInputRunning , readInputRunning
          where resInputRunning : direction (interfaceₚ (reservoir numNodes 3)) resOutput
                resInputRunning = readOutput , inputWeights , reservoirWeights , false
                readInputRunning : RunningInput numNodes
                readInputRunning = resOutput
                str = "GOING. readout layer output to res:\n"
                      ++ Matrix.showVec readOutput
        innerInputsFrom (lorTrainingOutput , _ , _ , resOutput , CD) dir = tt , inj₁ tt , CD , resInputTraining , CDI resOutput (outToVec lorTrainingOutput)
           where resInputTraining : direction (interfaceₚ (reservoir numNodes 3)) resOutput
                 resInputTraining = Lorenz.outToVec lorTrainingOutput , inputWeights , reservoirWeights , false

lorenzReservoir : 
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (touchSteps : ℕ) →
  (dt : ℝ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  DynamicalSystem
lorenzReservoir numNodes trainingSteps touchSteps dt inputWeights reservoirWeights = 
  install (preLorRes numNodes trainingSteps touchSteps dt inputWeights reservoirWeights) 
          (OuterOutput numNodes)
          (lorenzReservoirWiringDiagram numNodes inputWeights reservoirWeights)

lorenzResSeq :
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (touchSteps : ℕ) →
  (lorenzInitialConditions : ℝ × ℝ × ℝ ) →
  (dt : ℝ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  Stream (OuterOutputType numNodes) _
lorenzResSeq numNodes trainingSteps touchSteps ( ix , iy , iz ) dt inputWeights reservoirWeights = 
  run (lorenzReservoir numNodes trainingSteps touchSteps dt inputWeights reservoirWeights)
      auto
      ((xnt ix , ynt iy , znt iz) , ((xnt (ix + 3.0) , ynt (iy + 3.0) , znt (iz + 3.0))) , 0 , (Res (Vec.replicate 0.0)) , Coll (Collecting 0 Vec.[] Vec.[]))

lorenzResList : 
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (touchSteps : ℕ) →
  (outputLength : ℕ) →
  (lorenzInitialConditions : ℝ × ℝ × ℝ) →
  (dt : ℝ)
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  Vec (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ) outputLength
lorenzResList numNodes trainingSteps touchSteps outputLength lorenzInitialConditions dt inputWeights reservoirWeights = 
    Vec.map discr (take outputLength ∘ drop (trainingSteps +ℕ touchSteps) $ lorenzResSeq numNodes trainingSteps touchSteps lorenzInitialConditions dt inputWeights reservoirWeights)
       where discr : OuterOutputType numNodes → (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
             discr (inj₁ x) = x
             discr (inj₂ tt) = 0.0 , 0.0 , 0.0 , 0.0 , 0.0 , 0.0 
  