{-# OPTIONS --cubical --sized-types #-}

module Cubical.LensIsMealyMachine where

open import Dynamical.MealyMachine
open import Dynamical.System
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Everything
open import CategoryData.Everything
open import Cubical.Data.Sigma.Properties
open import Cubical.Proofs
open import Cubical.Foundations.HLevels
open Polynomial
open Lens
open import Data.Product hiding (Σ-syntax)

input : (p : Polynomial) → {isMonomialΣ p} → Set
input _ {i , _} = i

lensIsDynamics : MealyMachine ≡ (Σ[ dyn ∈ DynamicalSystem ] isMonomialΣ (DynamicalSystem.interface dyn))
lensIsDynamics = isoToPath (iso f f⁻ (λ b → {!   !}) λ a → {!  !})
    where
        f : MealyMachine → Σ[ dyn ∈ DynamicalSystem ] isMonomialΣ (DynamicalSystem.interface dyn)
        f (MkMealyMachine State Input Output run) = 
            mkdyn (State × Input)
                  (monomial Output Input) 
                  ((λ { (state , lastInput) → snd (run state lastInput)  } ) 
                  ⇆ 
                  λ { (state , lastInput ) newInput →  let newState = fst (run state newInput) in newState , newInput } )
            , Input , refl
        f⁻ : Σ[ dyn ∈ DynamicalSystem ] isMonomialΣ (DynamicalSystem.interface dyn) → MealyMachine
        f⁻ (mkdyn st interface (readout ⇆ update) , isMon) =
            MkMealyMachine (st × (input interface {isMon})) (input interface {isMon}) (position interface) runner
              where inpType = fst isMon
                    runner : st × inpType → inpType → (st × inpType) × position interface
                    runner (oldSt , lastInp) newInp = (newState , newInp) , readout newState
                        where dir≡inp : inpType ≡ direction interface (readout oldSt)
                              dir≡inp = sym (snd isMon {p = readout oldSt})
                              newState : st
                              newState = update oldSt (transport dir≡inp newInp) 