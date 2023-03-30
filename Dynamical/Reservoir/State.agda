{-# OPTIONS --sized-types #-}

module Dynamical.Reservoir.State where

open import Data.Float renaming (Float to ℚ)
open import Data.Nat
open import Dynamical.Reservoir.Matrix
open import Data.Vec hiding (_>>=_)
open import Data.List
open import Level
import Category.Monad.Reader

OutputWeights : (numNodes systemDim : ℕ) → Set
OutputWeights numNodes systemDim = Matrix ℚ numNodes systemDim

-- Actually I don't think there's a way to get around the TrainingState having access to
-- the outputWeights, but I think the RunningState might be spared this fate.

record TrainingState (numNodes : ℕ) (systemDim : ℕ) : Set where
  constructor Training
  field
    nodeStates : Vec ℚ numNodes
    statesHistory : List (Vec ℚ numNodes)
    outputWeights : OutputWeights numNodes systemDim
    counter : ℕ

record RunningState (numNodes : ℕ) (systemDim : ℕ) : Set where
  constructor Running
  field
    nodeStates : Vec ℚ numNodes
    outputWeights : OutputWeights numNodes systemDim
    counter : ℕ



data ReservoirState (numNodes : ℕ) (systemDim : ℕ)  : Set where
  T : TrainingState numNodes systemDim → ReservoirState numNodes systemDim
  R : RunningState numNodes systemDim → ReservoirState numNodes systemDim