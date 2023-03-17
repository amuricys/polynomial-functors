-- Dynamical/Plot/Plot.agda

{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Plot.Plot where

open import Data.Float
open import Data.Unit
open import Data.List as List using (List)
open import Data.String
open import Data.Product

open import IO.Primitive

postulate
  plotDynamics  : Float → List Float → List Float → IO ⊤

{-# FOREIGN GHC import HsPlot #-}
{-# COMPILE GHC plotDynamics = plotToFile #-}

open import Dynamical.LotkaVolterra
open import Dynamical.HodgkinHuxley
import Data.Vec as Vec
open import Dynamical.Plot.Optparse

rest : DynamicalSystem → List Float → IO ⊤
rest LotkaVolterra param = do
            let dyn = Vec.toList lvList
            let r , f = List.unzip dyn
            plotDynamics 0.1 r f
rest HodgkinHuxley param = do
  let dyn = Vec.toList hhList
  plotDynamics 0.1 dyn dyn

main : IO ⊤
main = do
  mkopt sys param ← parseOptions
  rest sys param
