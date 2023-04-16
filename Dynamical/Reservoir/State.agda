{-# OPTIONS --sized-types #-}

module Dynamical.Reservoir.State where

open import Data.Float renaming (Float to ℝ)
open import Data.Nat
open import Dynamical.Matrix.Core
open import Data.Vec hiding (_>>=_)
open import Data.List
open import Level
import Category.Monad.Reader

OutputWeights : (numNodes systemDim : ℕ) → Set
OutputWeights numNodes systemDim = Matrix ℝ systemDim numNodes

InputWeights : (numNodes systemDim : ℕ) → Set
InputWeights numNodes systemDim = Matrix ℝ numNodes systemDim

ReservoirWeights : (numNodes : ℕ) → Set
ReservoirWeights numNodes = Matrix ℝ numNodes numNodes

record TrainingState (numNodes : ℕ) (systemDim : ℕ) : Set where
  constructor Training
  field
    statesHistory : List (Vec ℝ numNodes)
    outputWeights : OutputWeights numNodes systemDim
    counter : ℕ

-- There's some states we want frozen. Is there a way to achieve this without 
-- needing inputs to be provided? Maybe yet another dynamical system that
-- is somehow understood to be constant? For example, We don't want the readout layer to
-- access the output weights as a state so as to not change them when it's running.
-- We also don't want the reservoir to access its input weights.
record ReservoirState (numNodes : ℕ) : Set where
  constructor Res
  field
    nodeStates : Vec ℝ numNodes

record CollectingDataState (numNodes : ℕ) (systemDim : ℕ) : Set where
  constructor Collecting
  field
    statesHistory : List (ReservoirState numNodes)
    systemHistory : List (Vec ℝ systemDim)
    outputWeights : OutputWeights numNodes systemDim
    counter : ℕ


record RunningState (numNodes : ℕ) (systemDim : ℕ) : Set where
  constructor Running
  field
    outputWeights : OutputWeights numNodes systemDim
    reservoirState : ReservoirState numNodes

data ReadoutLayerState (numNodes : ℕ) (systemDim : ℕ) : Set where
  Coll : CollectingDataState numNodes systemDim → ReadoutLayerState numNodes systemDim
  Run : RunningState numNodes systemDim → ReadoutLayerState numNodes systemDim
