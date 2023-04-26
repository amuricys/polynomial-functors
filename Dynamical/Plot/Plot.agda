-- Dynamical/Plot/Plot.agda

{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Plot.Plot where

open import Data.Float
open import Data.Unit
open import Data.List as List using (_∷_ ; [] ; List ; unzip ; [_] ) 
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
open import Data.Float as Float
open import Data.Integer
open import Data.Nat
open import Data.Maybe using (just ; nothing)
open import Data.Empty
open import Level
open import Data.Product

floor : Float → IO ℕ
floor f with ⌊ f ⌋
... | just x = return ∣ x ∣
... | nothing = do
         lift tt ← IO.run {Level.zero} $ IO.putStrLn ("Error: Invalid floating-point number for floor function: " ++ Float.show f )
         IO.run $ IO.pure 0

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
rest Reservoir (rdimf ∷ trainStepsf ∷ totalSeqStepsf ∷ lorinitx ∷ lorinity ∷ lorinitz ∷ dt ∷ []) = do
  rdim ← floor rdimf
  trainSteps ← floor trainStepsf 
  totalSeqSteps ← floor totalSeqStepsf 
      -- variance etc
  inputWeights ← IO.run $ initInputWeights rdim 3
  resWeights ← IO.run $ initReservoirWeights rdim
  collState ← IO.run $ initCollecting rdim 3
  let resVec = lorenzResList rdim trainSteps totalSeqSteps ( lorinitx , lorinity , lorinitz ) dt inputWeights resWeights collState
      x , yzabc = fromSigma (List.unzip (List.drop trainSteps $ Vec.toList resVec))
      y , zabc = fromSigma (List.unzip yzabc)
      z , abc = fromSigma (List.unzip zabc)
      a , bc = fromSigma (List.unzip abc)
      b , c = fromSigma (List.unzip bc)
  plotDynamics 0.1 (("actual_x", x) ∷ ("actual_y", y) ∷ ("actual_z", z) ∷ ("pred_x", a) ∷ ("pred_y", b) ∷ ("pred_z", c) ∷ []) 
rest Reservoir _ = do 
  lift tt ← IO.run {Level.zero} $ IO.putStrLn ("Error: missing parameters for reservoir")
  IO.run $ IO.pure tt
main : IO ⊤
main = do
  mkopt sys param ← parseOptions
  rest sys param
   