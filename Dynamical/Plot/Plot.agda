-- Dynamical/Plot/Plot.agda

{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Plot.Plot where

open import Agda.Builtin.IO
open import Data.Float
open import Data.Unit
open import Data.List as List using (List)
open import Data.Product

postulate
  plotDynamics  : Float → List Float → List Float → IO ⊤

{-# FOREIGN GHC import HsPlot #-}
{-# COMPILE GHC plotDynamics = plotToFile #-}

open import Dynamical.LotkaVolterra
import Data.Vec as Vec

main = do
  let dyn = Vec.toList lvList
  let r , f = List.unzip dyn
  plotDynamics 0.1 r f