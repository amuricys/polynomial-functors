{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Reservoir.ModeDependentNew where

open import Dynamical.System
open import Data.Product using (_×_; _,_)
open import Data.Sum
open import Data.Unit
open import Data.Nat renaming (_+_ to _+ℕ_ ; _∸_ to _-ℕ_)
open import Data.Float renaming (Float to ℝ; tanh to tanh1; show to showf) hiding (⌊_⌋)
open import CategoryData.Everything renaming (_*_ to _*p_ ; _+_ to _+p_; Y to Y')
open import Codata.Stream using (Stream ; take ; drop)
open import Dynamical.Matrix.Everything as Matrix using (Matrix ; _*ⱽᴹ_ ; _*ᴹⱽ_ ; _*ᴹ_ ; _+ᴹ_ ; _+ⱽ_ ; _ᵀ ; _⁻¹ ; _*ˢᴹ_ ; eye)
open import Dynamical.Reservoir.StateNew
open import Dynamical.Lorenz as Lorenz
open import Data.Vec as Vec using (Vec ; map ; _∷_ ; [])
open import Data.Bool using (if_then_else_ ; Bool)
open import Data.List using (List ; reverse)
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

data ReservoirOutput (systemDim : ℕ) : Set where
    stillColl : ReservoirOutput systemDim
    stillTouch : ReservoirOutput systemDim
    predicting : Vec ℝ systemDim → ReservoirOutput systemDim

activate : {numNodes systemDim : ℕ} (inputWeights : InputWeights numNodes systemDim) (reservoirWeights : ReservoirWeights numNodes) → (nodeStates : Vec ℝ numNodes) (inputSequence : Vec ℝ systemDim) → Vec ℝ numNodes
activate {numNodes} {systemDim} inputWeights reservoirWeights nodeStates inputSequence = reservoirActivations
  where inputDynamic : Vec ℝ numNodes
        inputDynamic = inputWeights *ᴹⱽ inputSequence
        newReservoirStates : Vec ℝ numNodes
        newReservoirStates = reservoirWeights *ᴹⱽ nodeStates
        reservoirActivations : Vec ℝ numNodes
        reservoirActivations = Vec.map tanh1 (newReservoirStates +ⱽ inputDynamic)

reservoir : (numNodes systemDim trainingSteps touchingSteps : ℕ)  (inputWeights : InputWeights numNodes systemDim) (reservoirWeights : ReservoirWeights numNodes) → DynamicalSystem
reservoir numNodes systemDim trainingSteps touchingSteps inputWeights reservoirWeights = mkdyn (ReservoirState numNodes systemDim) interface (readout ⇆ update)
  where interface : Polynomial
        interface = monomial (ReservoirOutput systemDim) (Vec ℝ systemDim)
        readout : ReservoirState numNodes systemDim → ReservoirOutput systemDim
        readout (Coll nodeStates counter statesHistory systemHistory) = stillColl
        readout (Touch nodeStates counter outputWeights) = stillTouch
        readout (Go nodeStates outputWeights) = predicting (outputWeights ᵀ *ᴹⱽ nodeStates) 
        update : ReservoirState numNodes systemDim → Vec ℝ systemDim → ReservoirState numNodes systemDim
        update (Coll nodeStates counter statesHistory systemHistory) inputSequence = 
            if is-< counter trainingSteps then keepCollecting else trainThenTouch
              where keepCollecting : ReservoirState numNodes systemDim
                    keepCollecting = Coll newStates (1 +ℕ counter) (nodeStates ∷ statesHistory) (inputSequence ∷ systemHistory)
                      where newStates : Vec ℝ numNodes 
                            newStates = activate inputWeights reservoirWeights nodeStates inputSequence
                    trainThenTouch : ReservoirState numNodes systemDim
                    trainThenTouch = Touch (Vec.replicate 0.0) 0 trainedOutputWeights
                      where ridge = 0.01
                            statesHist : Matrix ℝ counter numNodes
                            statesHist = Matrix.𝕄 $ Vec.reverse statesHistory
                            systemHist : Matrix ℝ counter systemDim
                            systemHist = Matrix.𝕄 $ Vec.reverse systemHistory
                            trainedOutputWeights : OutputWeights numNodes systemDim
                            trainedOutputWeights = (statesHist ᵀ *ᴹ statesHist +ᴹ ridge *ˢᴹ eye)⁻¹ *ᴹ (statesHist ᵀ *ᴹ systemHist)
        update (Touch nodeStates counter outputWeights) inputSequence =
            if is-< counter (touchingSteps -ℕ 1) then keepTouching else go -- minus 1 because one step is transitionary
              where keepTouching : ReservoirState numNodes systemDim
                    keepTouching = Touch (activate inputWeights reservoirWeights nodeStates inputSequence) (1 +ℕ counter) outputWeights
                    go : ReservoirState numNodes systemDim
                    go = Go (activate inputWeights reservoirWeights nodeStates inputSequence)
                            outputWeights
        update ro@(Go nodeStates outputWeights) inputSequence =
            Go newNodeStates outputWeights
          where reservoirDynamic : Vec ℝ numNodes
                reservoirDynamic = reservoirWeights *ᴹⱽ nodeStates
                out : Vec ℝ systemDim
                out = outputWeights ᵀ *ᴹⱽ nodeStates
                inputDynamic : Vec ℝ numNodes
                inputDynamic = inputWeights *ᴹⱽ out
                newNodeStates = Vec.map tanh1 (reservoirDynamic +ⱽ inputDynamic)
                

preLorRes : (numNodes trainingSteps touchSteps : ℕ) → (dt : ℝ) → InputWeights numNodes 3 → ReservoirWeights numNodes → DynamicalSystem
preLorRes numNodes trainingSteps touchSteps dt inputWeights reservoirWeights = 
  -- Training system
  lorenz dt &&& 
  -- Test system
  lorenz dt &&&
  -- Reservoir of dynamics + readout layer
  reservoir numNodes 3 trainingSteps touchSteps inputWeights reservoirWeights

open DynamicalSystem
lrWiringDiagram : (numNodes trainingSteps touchSteps : ℕ) → (dt : ℝ) → (iw : InputWeights numNodes 3) → (rw : ReservoirWeights numNodes) → 
        Lens (interface (preLorRes numNodes trainingSteps touchSteps dt iw rw)) (emitter (ReservoirOutput 3 × (X × Y × Z)))
lrWiringDiagram numNodes trainingSteps touchSteps dt iw rw = outerOutputsFrom ⇆ innerInputsFrom
    where outerOutputsFrom : (X × Y × Z) × (X × Y × Z) × ReservoirOutput 3 → ReservoirOutput 3 × (X × Y × Z)
          outerOutputsFrom (_ , test , ro) = ro , test
          innerInputsFrom : (X × Y × Z) × (X × Y × Z) × ReservoirOutput 3 → ⊤ → (⊤ × ⊤ × Vec ℝ 3)
          innerInputsFrom (lorOut , lorTestOut , stillColl) tt = tt , tt , Lorenz.outToVec lorOut
          innerInputsFrom (lorOut , lorTestOut , stillTouch) tt = tt , tt , Lorenz.outToVec lorTestOut
          innerInputsFrom (lorOut , lorTestOut , predicting x₁) tt = tt , tt , x₁

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
          (emitter (ReservoirOutput 3 × (X × Y × Z)))
          (lrWiringDiagram numNodes trainingSteps touchSteps dt inputWeights reservoirWeights)

lorenzResSeq :
  (numNodes : ℕ) →
  (trainingSteps : ℕ) →
  (touchSteps : ℕ) →
  (lorenzInitialConditions : ℝ × ℝ × ℝ ) →
  (dt : ℝ) →
  (inputWeights : InputWeights numNodes 3) →
  (reservoirWeights : ReservoirWeights numNodes) → 
  Stream (ReservoirOutput 3 × (X × Y × Z)) _
lorenzResSeq numNodes trainingSteps touchSteps ( ix , iy , iz ) dt inputWeights reservoirWeights = 
  run (lorenzReservoir numNodes trainingSteps touchSteps dt inputWeights reservoirWeights)
      auto
      ((xnt ix , ynt iy , znt iz) , (xnt (ix + 3.0) , ynt (iy + 3.0) , znt (iz + 3.0)) , Coll (Vec.replicate 0.0) 0 [] [])

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
    Vec.map discr ∘ take outputLength ∘ drop (trainingSteps +ℕ touchSteps +ℕ 1 {- we drop one more bc we dont want the transition -}) $ (lorenzResSeq numNodes trainingSteps touchSteps lorenzInitialConditions dt inputWeights reservoirWeights)
       where discr : (ReservoirOutput 3 × (X × Y × Z)) → (ℝ × ℝ × ℝ × ℝ × ℝ × ℝ)
             discr (stillColl , xnt actual_x , ynt actual_y , znt actual_z) = 0.0 , 0.0 , 0.0 , actual_x , actual_y , actual_z
             discr (stillTouch , xnt actual_x , ynt actual_y , znt actual_z) = 0.0 , 0.0 , 0.0 , actual_x , actual_y , actual_z
             discr (predicting (pred_x ∷ pred_y ∷ pred_z ∷ []) , xnt actual_x , ynt actual_y , znt actual_z) = pred_x , pred_y , pred_z , actual_x , actual_y , actual_z
  