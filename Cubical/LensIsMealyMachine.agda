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
open import Function
input : (p : Polynomial) → {isMonomialΣ p} → Set
input _ {i , _} = i


-- go : {State Input Output : Set} → Lens (selfMonomial (State × Input)) (monomial Output Input) → MealyMachine {State} {Input} {Output}
-- go {State} {Input} {Output}  (readout ⇆ update) =
--   mkmealy runner 
--     where runner : State → Input → State × Output
--           runner oldState input = newState , output
--               where updated = update (oldState , input) input
--                     newState : State
--                     newState = fst (update (oldState , input) input)
--                     output : Output
--                     output = readout (oldState , input)
-- back : {State Input Output : Set} → MealyMachine {State} {Input} {Output} → Lens (selfMonomial (State × Input)) (monomial Output Input)
-- back {State} {Input} {Output}  (mkmealy runner)  = readout ⇆ update
--    where readout : State × Input → Output
--          readout (state , input) = snd (runner state input)
--          update : State × Input → Input → State × Input
--          update (state , oldInput) newInput = fst (runner state oldInput) , newInput 


open import Data.Unit
open import Data.Sum

-- A dynamical system lens (domain polynomial is selfMonomial) where the interface is a monomial is the same as a moore machine.
simpleLensIsMealyMachine : {State Input Output : Set} → Lens (selfMonomial State) (linear Output ^ linear Input) ≡ MealyMachine {State} {Input} {Output}
simpleLensIsMealyMachine {State} {Input} {Output} = isoToPath (iso hehef 
                                                                   heheb 
                                                                   (λ b → refl) 
                                                                   (λ b → refl))
      where hehef : Lens (selfMonomial State) (linear Output ^ linear Input) → MealyMachine
            hehef (f ⇆ f♯) = mkmealy (λ x x₁ → (f♯ x (x₁ , (tt , {!  tt !}))) , proj₁ (f x x₁))
            heheb : MealyMachine → Lens (selfMonomial State) (linear Output ^ linear Input)
            heheb (mkmealy runner) = (λ x index → (snd (runner x index)) , (λ _ → inj₁ tt)) ⇆ (λ fromPos _ → fromPos)

-- lensIsDynamics : MealyMachine ≡ (Σ[ dyn ∈ DynamicalSystem ] isMonomialΣ (DynamicalSystem.interface dyn))
-- lensIsDynamics = isoToPath (iso f f⁻ (λ b → {!   !}) λ a → {!  !})
--     where
--         f : MealyMachine → Σ[ dyn ∈ DynamicalSystem ] isMonomialΣ (DynamicalSystem.interface dyn)
--         f (MkMealyMachine State Input Output run) = 
--             mkdyn (State × Input)
--                   (monomial Output Input) 
--                   ((λ { (state , lastInput) → snd (run state lastInput)  } ) 
--                   ⇆ 
--                   λ { (state , lastInput ) newInput →  let newState = fst (run state newInput) in newState , newInput } )
--             , Input , refl
--         f⁻ : Σ[ dyn ∈ DynamicalSystem ] isMonomialΣ (DynamicalSystem.interface dyn) → MealyMachine
--         f⁻ (mkdyn st interface (readout ⇆ update) , isMon) =
--             MkMealyMachine (st × (input interface {isMon})) (input interface {isMon}) (position interface) runner
--               where inpType = fst isMon
--                     runner : st × inpType → inpType → (st × inpType) × position interface
--                     runner (oldSt , lastInp) newInp = (newState , newInp) , readout newState
--                         where dir≡inp : inpType ≡ direction interface (readout oldSt)
--                               dir≡inp = sym (snd isMon)
--                               newState : st
--                               newState = update oldSt (transport dir≡inp newInp)    