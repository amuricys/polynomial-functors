{-# OPTIONS --guardedness #-}

module Dynamical.Plot.Optparse where

open import Agda.Builtin.IO
open import Agda.Builtin.Float
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.List

data DynamicalSystem : Set where
  LotkaVolterra : DynamicalSystem
  HodgkinHuxley : DynamicalSystem
  Lorenz : DynamicalSystem

record Options : Set where
  constructor mkopt
  field
    system  : DynamicalSystem
    params : List Float

{-# FOREIGN GHC 
import OptparseHs
#-}

{-# COMPILE GHC DynamicalSystem = data DynamicalSystem (LotkaVolterra | HodgkinHuxley | Lorenz) #-}
{-# COMPILE GHC Options = data Options (Options) #-}

postulate 
  parseOptions : IO Options
{-# COMPILE GHC parseOptions = parseOptions #-}