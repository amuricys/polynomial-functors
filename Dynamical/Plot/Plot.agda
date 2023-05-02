-- Dynamical/Plot/Plot.agda

{-# OPTIONS --sized-types --guardedness #-}

module Dynamical.Plot.Plot where

open import Data.Float 
open import Data.Unit
open import Data.List as List using (_∷_ ; [] ; List ; unzip ; [_] ) renaming (map to listMap)
open import Data.Product as P hiding (_×_) renaming (_,_ to _,p_)
open import Data.String
open import Dynamical.Matrix.Core
open import Dynamical.Reservoir.State

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
open import Data.Maybe using (just ; nothing ; Maybe)
open import Data.Empty
import Level 
open import Data.Product using (_,_)

floor : Float → IO ℕ
floor f with ⌊ f ⌋
... | just x = return ∣ x ∣
... | nothing = do
         Level.lift tt ← IO.run {Level.zero} $ IO.putStrLn ("Error: Invalid floating-point number for floor function: " ++ Float.show f )
         IO.run $ IO.pure 0

open import Data.String as S

showVec : ∀ {m} → Vec.Vec Float m → String 
showVec v = "[" S.++ go v S.++ "]"
  where go : ∀ {m} → Vec.Vec Float m → String
        go Vec.[] = ""
        go (x Vec.∷ Vec.[]) = Data.Float.show x
        go (x Vec.∷ v) = Data.Float.show x S.++ ", " S.++ go v

showList : List Float → String 
showList v = "[" S.++ go v S.++ "]"
  where go : List Float → String
        go [] = ""
        go (x ∷ []) = Data.Float.show x
        go (x ∷ v) = Data.Float.show x S.++ ", " S.++ go v
 
showMatrix : ∀ {n m} → Matrix Float n m → String
showMatrix {.ℕ.zero} {m} (𝕄 Vec.[]) = ""
showMatrix {.(ℕ.suc _)} {m} (𝕄 (v Vec.∷ vs)) = showVec v S.++ "\n" S.++ showMatrix (𝕄 vs)

showListMatrix : ∀ {n} → List (Vec.Vec Float n) → String
showListMatrix [] = ""
showListMatrix (v ∷ vs) = showVec v S.++ "\n" S.++ showListMatrix vs


printMatrix : ∀ {n m} → Matrix Float n m → IO ⊤
printMatrix m = do
  _ ← IO.run {Level.zero} $ IO.putStr $ showMatrix m
  IO.run $ IO.pure tt

printMatrices : ∀ {n m} → List (Matrix Float n m) → IO ⊤
printMatrices (n ∷ ns) = do
  _ ← printMatrix n
  _ ← IO.run {Level.zero} $ IO.putStrLn ""
  printMatrices ns
printMatrices [] = IO.run $ IO.pure tt

printOneMatrix : ∀ {n m} → List (Matrix Float n m) → IO ⊤
printOneMatrix (n ∷ ns) = do
  _ ← printMatrix n
  IO.run $ IO.pure tt
printOneMatrix [] = IO.run $ IO.pure tt

printLists : List (Float P.× Float P.× Float) → IO ⊤
printLists ((x , y , z) ∷ ns) = do
  _ ← IO.run {Level.zero} $ IO.putStrLn $ "(" S.++ Data.Float.show x S.++ ", " S.++ Data.Float.show y S.++ ", " S.++ Data.Float.show y S.++ ")"
  printLists ns
printLists [] = IO.run $ IO.pure tt

printMatrixAsList : ∀ {n} → List (Vec.Vec Float n) → IO ⊤
printMatrixAsList m = do
  _ ← IO.run {Level.zero} $ IO.putStr $ showListMatrix m
  IO.run $ IO.pure tt

printMatricesAsLists : ∀ {n} → List (List (Vec.Vec Float n)) → IO ⊤
printMatricesAsLists (n ∷ ns) = do
  _ ← printMatrixAsList n
  _ ← IO.run {Level.zero} $ IO.putStrLn ""
  printMatricesAsLists ns
printMatricesAsLists [] = IO.run $ IO.pure tt

printOneMatrixAsListFromList : ∀ {n} → List (List (Vec.Vec Float n)) → IO ⊤
printOneMatrixAsListFromList (_ ∷ n ∷ ns) = do
  _ ← printMatrixAsList n
  IO.run $ IO.pure tt
printOneMatrixAsListFromList _ = IO.run $ IO.pure tt

-- bigUnzip : ∀ {A B C D E F G H I : Set} → List (A P.× B P.× C P.× D P.× E P.× F P.× G P.× H P.× I) → 
--            (List A P.× List B P.× List C P.× List D P.× List E P.× List F P.× List G P.× List H P.× List I)
-- bigUnzip [] =  [] ,p [] ,p [] ,p [] ,p [] ,p [] ,p [] ,p [] ,p [] 
-- bigUnzip ((A ,p B ,p C ,p D ,p E ,p F ,p G ,p H ,p I ) ∷ l) = {! bigUnzip   !}

rest : SystemParams → IO ⊤
rest (ReservoirParams rdim trainSteps touchSteps outputLength lorinitx lorinity lorinitz dt₁ variance) = do 
  let rdim = 3

  -- variance etc
  inputWeights ← IO.run $ initInputWeights 0.0316 rdim 3
  resWeights ← IO.run $ initReservoirWeights 0.0632 rdim
  let 
      inputWeights = 𝕄 ((-0.064975537042022 Vec.∷ -0.065251741398635 Vec.∷ 0.058517783986069 Vec.∷ Vec.[]) Vec.∷ 
                        (0.076889134463803 Vec.∷ -0.013081902744785 Vec.∷ 0.009235160871493 Vec.∷ Vec.[]) Vec.∷ 
                        (0.027362146117304 Vec.∷ 0.007721283721158 Vec.∷ 0.042541281223982 Vec.∷ Vec.[]) Vec.∷ 
                        Vec.[])
      resWeights = 𝕄 ((0.197316884195857 Vec.∷ -0.574663634125314 Vec.∷ 0.784674814076449 Vec.∷ Vec.[]) Vec.∷ 
                      (0.145047612964489 Vec.∷ 0.407975310337146 Vec.∷ -0.029230453464976 Vec.∷ Vec.[]) Vec.∷ 
                      (1.227628071998505 Vec.∷ 0.636586542258952 Vec.∷ 0.623759334372951 Vec.∷ Vec.[]) Vec.∷ 
                      Vec.[])
      resVec = lorenzResList rdim trainSteps touchSteps outputLength ( lorinitx , lorinity , lorinitz ) dt₁ inputWeights resWeights
      x , yzabc = fromSigma (List.unzip (Vec.toList resVec))
      y , zabc = fromSigma (List.unzip yzabc)
      z , abc = fromSigma (List.unzip zabc)
      pred_x , bc = fromSigma (List.unzip abc)
      pred_y , co = fromSigma (List.unzip bc)
      pred_z , ohs = fromSigma (List.unzip co)
      o , hs = fromSigma (List.unzip ohs)
      h , s = fromSigma (List.unzip hs)
  _ ← IO.run {Level.zero} $ IO.putStrLn "system history:"
  _ ← printOneMatrixAsListFromList s
  _ ← IO.run {Level.zero} $ IO.putStrLn "reservoir state history:"
  _ ← printOneMatrixAsListFromList (listMap (listMap ReservoirState.nodeStates) h)
  _ ← IO.run {Level.zero} $ IO.putStrLn "output weights history (should be the same):"
  _ ← printOneMatrix o
  _ ← IO.run {Level.zero} $ IO.putStrLn "predictions:"
  _ ← printLists $ List.zip pred_x $ List.zip pred_y pred_z
  plotDynamics 0.1 (("actual_x", x) ∷ ("actual_y", y) ∷ ("actual_z", z) ∷ ("pred_x", pred_x) ∷ ("pred_y", pred_y) ∷ ("pred_z", pred_z) ∷ []) 
rest (LorenzParams lorinitx lorinity lorinitz dt₁) = do 
  let x , yz = fromSigma (List.unzip (Vec.toList $ lorenzList lorinitx lorinity lorinitz dt₁))
  let y , z = fromSigma (List.unzip yz)
  plotDynamics 0.1 (("x", x) ∷ ("y", y) ∷ ("z", z) ∷ [])
rest HodgkinHuxleyParams = do 
  let dyn = Vec.toList hhList
  plotDynamics 0.1 [( "voltage" , dyn )]
rest (LotkaVolterraParams α β δ γ r0 f0 dt₁) = do 
  let dyn = Vec.toList $ lvList α β δ γ r0 f0
  let r , f = fromSigma (List.unzip dyn) 
  plotDynamics 0.1 (("rabbits", r) ∷ ("foxes", f) ∷ [])
-- rest Reservoir (rdimf ∷ trainStepsf ∷ touchStepsf ∷ outputLengthf ∷ lorinitx ∷ lorinity ∷ lorinitz ∷ dt ∷ []) = do
-- rest Reservoir params = do 
--   Level.lift tt ← IO.run {Level.zero} $ IO.putStrLn ("Error: missing parameters for reservoir. got: " S.++ showList params)
--   IO.run $ IO.pure tt
main : IO ⊤
main = do
  mkopt sys ← parseOptions
  rest sys
   