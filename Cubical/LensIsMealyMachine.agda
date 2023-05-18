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

open Polynomial
open Lens
open DynamicalSystem
open import Data.Product

input : {p : Polynomial} → {isMonomial p} → Set
input {mkpoly position₁ direction₁} {pr} = {!   !}

lensIsDynamics : MealyMachine ≡ DynamicalSystem -- (Σ[ dyn ∈ DynamicalSystem ] IsMonomial (interface dyn))
lensIsDynamics = isoToPath (iso f f⁻ (λ b → {!   !}) λ a → {!   !})
    where
        f : MealyMachine → DynamicalSystem -- [ dyn ∈ DynamicalSystem ] IsMonomial (interface dyn)
        f (MkMealyMachine State Input Output run) = 
            mkdyn (State × Input)
                  (monomial Output Input) 
                  ((λ { (state , lastInput) → snd (run state lastInput)  } ) 
                  ⇆ 
                  λ { (state , lastInput ) newInput →  let newState = fst (run state newInput) in newState , newInput } )

        -- record { State = State ; Input = Input ; Output = Output ; update = update ; readout = readout }
        --  = mkdyn State (monomial Output Input) (readout ⇆ update) , record { input = Input ; output = Output ; proof = refl }

        f⁻ : DynamicalSystem → MealyMachine
        f⁻ (mkdyn state (mkpoly position₁ direction₁) dynamics) = {!   !}

        -- f : MealyMachine → Σ[ dyn ∈ DynamicalSystem ] IsMonomial (interface dyn)
        -- f record { State = State ; Input = Input ; Output = Output ; update = update ; readout = readout }
        --  = mkdyn State (monomial Output Input) (readout ⇆ update) , record { input = Input ; output = Output ; proof = refl }

        -- f⁻ : (Σ[ dyn ∈ DynamicalSystem ] IsMonomial (interface dyn)) → MealyMachine
        -- f⁻ (mkdyn state interface dynamics , record { input = input ; output = output ; proof = proof })
        -- -- state → input → state
        --     = record { State = state ; Input = input ; Output = output ; update = J (λ y x → state → input → state) {! mapDirection dynamics  !} proof ; readout = {!  mapPosition dynamics !} }
            -- f⁻ (mkdyn state₁ interface₁ dynamics₁ , snd₁) = ? -- record { State = {! fst₁  !} ; Input = {!   !} ; Output = {!   !} ; update = {!   !} ; readout = {!   !} } 
        -- (mkdyn state interface dynamics) 
        --     = record { State = state ; Input = {! direction interface   !} ; Output = position interface ; update = {!  mapDirection dynamics !} ; readout = mapPosition dynamics }

-- lensIsDynamicsInitialed : chine ≡ 
 