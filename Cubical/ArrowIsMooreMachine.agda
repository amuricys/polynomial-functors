{-# OPTIONS --cubical --sized-types #-}

module Cubical.ArrowIsMooreMachine where

open import Dynamical.MooreMachine
open import Dynamical.System
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Core.Everything
open import Common.CategoryData
open import Cubical.Data.Sigma.Properties

open Polynomial
open Arrow
open DynamicalSystem

-- record IsMonomial (p : Polynomial): Set₁ where
--     field
--         input : Set
--         output : Set
--         proof : p ≡ monomial output input

record SimpleDynamicalSystem : Set₁ where
    constructor MkSimpleDynamicalSystem
    field
        state : Set -- S
        -- interface : Polynomial -- p
        input : Set
        output : Set
        dynamics : Arrow (selfMonomial state) (monomial output input) -- Sy^S → p

arrowIsDynamics : MooreMachine ≡ SimpleDynamicalSystem -- (Σ[ dyn ∈ DynamicalSystem ] IsMonomial (interface dyn))
arrowIsDynamics = isoToPath (iso f f⁻ (λ b → refl) λ a → refl)
    where
        f : MooreMachine → SimpleDynamicalSystem -- [ dyn ∈ DynamicalSystem ] IsMonomial (interface dyn)
        f (MkMooreMachine State Input Output update readout) = MkSimpleDynamicalSystem State Input Output (readout ⇄ update) 

        -- record { State = State ; Input = Input ; Output = Output ; update = update ; readout = readout }
        --  = MkDynamicalSystem State (monomial Output Input) (readout ⇄ update) , record { input = Input ; output = Output ; proof = refl }

        f⁻ : SimpleDynamicalSystem → MooreMachine
        f⁻ (MkSimpleDynamicalSystem state input output dynamics) = MkMooreMachine state input output (mapDirection dynamics) (mapPosition dynamics)

        -- f : MooreMachine → Σ[ dyn ∈ DynamicalSystem ] IsMonomial (interface dyn)
        -- f record { State = State ; Input = Input ; Output = Output ; update = update ; readout = readout }
        --  = MkDynamicalSystem State (monomial Output Input) (readout ⇄ update) , record { input = Input ; output = Output ; proof = refl }

        -- f⁻ : (Σ[ dyn ∈ DynamicalSystem ] IsMonomial (interface dyn)) → MooreMachine
        -- f⁻ (MkDynamicalSystem state interface dynamics , record { input = input ; output = output ; proof = proof })
        -- -- state -> input -> state
        --     = record { State = state ; Input = input ; Output = output ; update = J (λ y x → state → input → state) {! mapDirection dynamics  !} proof ; readout = {!  mapPosition dynamics !} }
            -- f⁻ (MkDynamicalSystem state₁ interface₁ dynamics₁ , snd₁) = ? -- record { State = {! fst₁  !} ; Input = {!   !} ; Output = {!   !} ; update = {!   !} ; readout = {!   !} } 
        -- (MkDynamicalSystem state interface dynamics) 
        --     = record { State = state ; Input = {! direction interface   !} ; Output = position interface ; update = {!  mapDirection dynamics !} ; readout = mapPosition dynamics }

-- arrowIsDynamicsInitialed : chine ≡ 