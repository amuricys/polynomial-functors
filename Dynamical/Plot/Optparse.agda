{-# OPTIONS --guardedness #-}

module Dynamical.Plot.Optparse where

open import Agda.Builtin.IO
open import Agda.Builtin.Float
open import Agda.Builtin.Nat renaming (Nat to ℕ)
open import Data.List


{-# FOREIGN GHC 
import OptparseHs
#-}

data SystemParams : Set where
  ReservoirParams : (rdim : ℕ) → 
                    (trainSteps touchSteps outputLength : ℕ) → 
                    (lorinitx lorinity lorinitz dt variance : Float) → 
                    SystemParams
  LorenzParams    : (lorinitx lorinity lorinitz dt : Float) → SystemParams
  HodgkinHuxleyParams : (dt : Float) → SystemParams
  LotkaVolterraParams : (α β δ γ r0 f0 dt : Float) → SystemParams
{-# COMPILE GHC SystemParams = data SystemParams
   (ReservoirParams | LorenzParams | HodgkinHuxleyParams | LotkaVolterraParams) #-}

record Options : Set where
  constructor mkopt
  field
    system  : SystemParams

{-# COMPILE GHC Options = data Options (Options) #-}

postulate 
  parseOptions : IO Options
{-# COMPILE GHC parseOptions = parseOptions #-} 