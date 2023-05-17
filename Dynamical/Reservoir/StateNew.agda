{-# OPTIONS --sized-types #-}

module Dynamical.Reservoir.StateNew where

open import Data.Float renaming (Float to ℝ)
open import Data.Nat
open import Dynamical.Matrix.Core
open import Data.Vec hiding (_>>=_)
open import Data.List
open import Level
import Category.Monad.Reader
open import Data.Bool

OutputWeights : (numNodes systemDim : ℕ) → Set
OutputWeights numNodes systemDim = Matrix ℝ numNodes systemDim

InputWeights : (numNodes systemDim : ℕ) → Set
InputWeights numNodes systemDim = Matrix ℝ numNodes systemDim

ReservoirWeights : (numNodes : ℕ) → Set
ReservoirWeights numNodes = Matrix ℝ numNodes numNodes

-- There's some states we want frozen. Is there a way to achieve this without 
-- needing inputs to be provided? Maybe yet another dynamical system that
-- is somehow understood to be constant? For example, We don't want the readout layer to
-- access the output weights as a state so as to not change them when it's running.
-- We also don't want the reservoir to access its input weights.
data ReservoirState (numNodes : ℕ) (systemDim : ℕ) : Set where
  Coll : (nodeStates : Vec ℝ numNodes)
         (counter : ℕ)
         (statesHistory : Vec (Vec ℝ numNodes) counter) 
         (systemHistory : Vec (Vec ℝ systemDim) counter) → 
         ReservoirState numNodes systemDim
  Touch : (nodeStates : Vec ℝ numNodes)
          (counter : ℕ)
          (outputWeights : OutputWeights numNodes systemDim) 
          →
          ReservoirState numNodes systemDim
  Go : (nodeStates : Vec ℝ numNodes)
       (outputWeights : OutputWeights numNodes systemDim)
       →
       ReservoirState numNodes systemDim
