{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Reservoir.ModeDependent where

open import Dynamical.System
open import Data.Product
open import Data.Nat renaming (_+_ to _+ℕ_)
open import Data.Float renaming (Float to ℝ; tanh to tanh1) hiding (⌊_⌋)
open import Common.CategoryData renaming (_*_ to _*p_ ; _+_ to _+p_) hiding (Y)
open import Dynamical.Reservoir.Matrix as Matrix
open import Dynamical.Reservoir.Initialize
open import Dynamical.Reservoir.State
open import Dynamical.Lorenz
open import Data.Vec hiding (_>>=_)
open import Data.List as List
open import Data.Bool using (if_then_else_ ; Bool)
open import Relation.Nullary.Decidable using (⌊_⌋)

open import Level

import Category.Monad.Reader
open import Category.Monad
is-≤ : ℕ → ℕ → Bool
is-≤ a b = ⌊ a Data.Nat.≤? b ⌋

tanh : ∀ {m n} → Matrix ℝ m n → Matrix ℝ m n
tanh = Matrix.map tanh1


activation : ∀ {m n q : ℕ} → Matrix ℝ m n → Matrix ℝ n q → Matrix ℝ m q 
activation nodeStates outputWeights = tanh (nodeStates *ᴹ outputWeights)

lorenzReservoir : {systemDim numNodes : ℕ} → (trainingSteps : ℕ) → Matrix ℝ systemDim numNodes → Matrix ℝ numNodes numNodes → DynamicalSystem
lorenzReservoir {systemDim} {numNodes} trainingSteps inputWeights reservoirWeights = 
  lorenz &&& reservoir
  where reservoir : DynamicalSystem
        reservoir = MkDynamicalSystem (ReservoirState numNodes systemDim) interface (readout ⇄ update)
          where interface : Polynomial
                interface = MkPoly (Vec ℝ systemDim) λ _ → Vec ℝ systemDim
                
                readout : ReservoirState numNodes systemDim → Vec ℝ systemDim
                readout (T (Training nodeStates _ outputWeights _)) = fromMatrix (activation (vecToRowMatrix nodeStates) outputWeights)
                              where fromMatrix : Matrix ℝ 1 systemDim → Vec ℝ systemDim
                                    fromMatrix (𝕄 (v ∷ [])) = v
                readout (R (Running nodeStates outputWeights _)) = fromMatrix (activation (vecToRowMatrix nodeStates) outputWeights)
                              where fromMatrix : Matrix ℝ 1 systemDim → Vec ℝ systemDim
                                    fromMatrix (𝕄 (v ∷ [])) = v
                update : ReservoirState numNodes systemDim → (Vec ℝ systemDim) → ReservoirState numNodes systemDim
                update (T (Training nodeStates statesHistory outputWeights counter)) i =
                  if is-≤ counter trainingSteps then 
                    T keepTraining else
                    R startPredicting
                  where 
                        keepTraining : TrainingState numNodes systemDim
                        keepTraining = Training newNodeStates (newNodeStates List.∷ statesHistory) outputWeights (counter +ℕ 1)
                          where newNodeStates : Vec ℝ numNodes
                                newNodeStates = {!   !}
                        -- The first input to the predicting state ought to be the predicted system's dynamics
                        -- after that, it loops back on itself
                        startPredicting : RunningState numNodes systemDim
                        startPredicting = Running (initialPredictionStates i) newOutputWeights (counter +ℕ 1)
                          where newOutputWeights : OutputWeights numNodes systemDim
                                newOutputWeights = {!   !}
                                initialPredictionStates : Vec ℝ systemDim → Vec ℝ numNodes
                                initialPredictionStates = {!   !}
                update (R (Running nodeStates outputWeights counter)) i = R (Running {! newNodeStates  !} outputWeights (counter +ℕ 1))
   
open import Level
open import Data.String using (String)
open import Data.Float renaming (Float to ℝ; tanh to tanh1) hiding (⌊_⌋)
open import Category.Monad.Reader ℝ 0ℓ as Q
open import Category.Monad.Reader String 0ℓ as S

hey2 : S.Reader String
hey2 =
  let open S.RawMonadReader S.ReaderMonadReader
  in 
  do
  num ← ask
  pure "hello"

hey3 : Q.Reader String
hey3 = let
  open Q.RawMonadReader Q.ReaderMonadReader
  in do
  num ← ask
  pure "hello"


  