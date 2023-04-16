-- Dynamical/Plot/Plot.agda

{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Plot.Plot where

open import Data.Float
open import Data.Unit
open import Data.List as List
open import Data.Product as P hiding (_×_) renaming (_,_ to _,p_)
open import Data.String

record _×_ (A B : Set) : Set where
  constructor _,_
  field
    fst : A
    snd : B

fromSigma : {A B : Set} → A P.× B → A × B
fromSigma ( a ,p b ) = a , b

open import IO.Primitive
open import Function
import IO

postulate
  plotDynamics  : Float → List (String × List Float) → IO ⊤

{-# FOREIGN GHC import HsPlot #-}
{-# COMPILE GHC plotDynamics = plotToFile #-}
{-# COMPILE GHC _×_ = data (,) ((,)) #-}

open import Dynamical.LotkaVolterra
open import Dynamical.HodgkinHuxley
open import Dynamical.Lorenz
open import Dynamical.Reservoir.ModeDependent
open import Dynamical.Reservoir.Initialize
import Data.Vec as Vec
open import Dynamical.Plot.Optparse

rest : DynamicalSystem → List Float → IO ⊤
rest LotkaVolterra param = do
            let dyn = Vec.toList lvList
            let r , f = fromSigma (List.unzip dyn)
            plotDynamics 0.1 (("rabbits", r) ∷ ("foxes", f) ∷ [])
rest HodgkinHuxley param = do
  let dyn = Vec.toList hhList
  plotDynamics 0.1 [( "voltage" , dyn )]
rest Lorenz param = do
  let x , yz = fromSigma (List.unzip (Vec.toList lorenzList))
  let y , z = fromSigma (List.unzip yz)
  plotDynamics 0.1 (("x", x) ∷ ("y", y) ∷ ("z", z) ∷ [])
rest Reservoir param = do
  inputWeights ← IO.run $ initInputWeights 500 3
  resWeights ← IO.run $ initReservoirWeights 500
  collState ← IO.run $ initCollecting 500 3
  let resList = lorenzResList 500 1000 inputWeights resWeights collState
      x , yzabc = fromSigma (List.unzip (Vec.toList resList))
      y , zabc = fromSigma (List.unzip yzabc)
      z , abc = fromSigma (List.unzip zabc)
      a , bc = fromSigma (List.unzip abc)
      b , c = fromSigma (List.unzip bc)
  plotDynamics 0.1 (("x", x) ∷ ("y", y) ∷ ("z", z) ∷ ("a", a) ∷ ("b", b) ∷ ("c", c) ∷ []) 

main : IO ⊤
main = do
  mkopt sys param ← parseOptions
  rest sys param
   