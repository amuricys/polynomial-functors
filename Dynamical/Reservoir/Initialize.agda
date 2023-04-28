{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Reservoir.Initialize where

open import Data.Float
import IO.Primitive as Prim
open import IO
open import Dynamical.Matrix.Everything
open import Data.Nat hiding (_*_)
open import Data.Vec hiding (_>>=_)
open import Dynamical.Reservoir.State


postulate primRandom : Prim.IO Float
{-# FOREIGN GHC import qualified System.Random as Random #-}
{-# COMPILE GHC primRandom = Random.randomIO #-}

random : IO Float
random = lift primRandom

postulate primNormal : Prim.IO Float
{-# FOREIGN GHC import qualified Data.Random.Normal as Normal #-}
{-# COMPILE GHC primNormal = Normal.normalIO #-}

normal : Float → IO Float
normal factor = do
  x ← lift primNormal 
  pure (factor * x)

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

normalVec : (factor : Float) (cols : ℕ) → IO (Vec Float cols)
normalVec factor zero = pure []
normalVec factor (suc n) = do
  x ← normal factor
  (λ k → x ∷ k ) <$> normalVec factor n

normalMatrix : (factor : Float) (rows : ℕ) → (cols : ℕ) → IO (Matrix Float rows cols)
normalMatrix factor rows cols = 𝕄 <$> rowTimes rows (normalVec factor cols) where
  rowTimes : (rows : ℕ) → IO (Vec Float cols) → IO (Vec (Vec Float cols) rows)
  rowTimes zero _ = pure []
  rowTimes (suc n) rowGenerator = do
    row ← rowGenerator
    (λ k → row ∷ k ) <$> rowTimes n rowGenerator

initInputWeights : (factor : Float) (numNodes systemDim : ℕ) → IO (InputWeights numNodes systemDim)
initInputWeights factor n s = do
  input ← normalMatrix factor n s
  pure input

initReservoirWeights : (factor : Float) (numNodes : ℕ) → IO (ReservoirWeights numNodes)
initReservoirWeights factor n = do
  res ← normalMatrix factor n n
  pure res
