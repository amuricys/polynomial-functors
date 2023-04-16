{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Reservoir.Initialize where

open import Agda.Builtin.Float
import IO.Primitive as Prim
open import IO
open import Dynamical.Matrix.Everything
open import Data.Nat
open import Data.Vec hiding (_>>=_)
open import Dynamical.Reservoir.State

random : IO Float
random = lift primRandom where

 postulate primRandom : Prim.IO Float
 {-# FOREIGN GHC import qualified System.Random as Random #-}
 {-# COMPILE GHC primRandom = Random.randomIO #-}

randomVec : (cols : ℕ) → IO (Vec Float cols)
randomVec zero = pure []
randomVec (suc n) = do
  x ← random
  (λ k → x ∷ k ) <$> randomVec n

randomMatrix : (rows : ℕ) → (cols : ℕ) → IO (Matrix Float rows cols)
randomMatrix rows cols = 𝕄 <$> rowTimes rows (randomVec cols) where
  rowTimes : (rows : ℕ) → IO (Vec Float cols) → IO (Vec (Vec Float cols) rows)
  rowTimes zero _ = pure []
  rowTimes (suc n) rowGenerator = do
    row ← rowGenerator
    (λ k → row ∷ k ) <$> rowTimes n rowGenerator


initCollecting : (numNodes systemDim : ℕ) → IO (CollectingDataState numNodes systemDim)
initCollecting n s = do
  output ← randomMatrix n s
  pure (Collecting 0 [] [] output)

initInputWeights : (numNodes systemDim : ℕ) → IO (InputWeights numNodes systemDim)
initInputWeights n s = do
  input ← randomMatrix n s
  pure input

initReservoirWeights : (numNodes : ℕ) → IO (ReservoirWeights numNodes)
initReservoirWeights n = do
  res ← randomMatrix n n
  pure res
