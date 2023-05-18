{-# OPTIONS --cubical --sized-types #-}

module Cubical.LensIsMooreMachine where

open import Cubical.Foundations.Everything
open import Cubical.Proofs
open import CategoryData.Everything
open import Data.Product
open import Data.Unit

record MooreMachine {State Input Output : Set} : Set where
    constructor mkMooreMachine
    field
        readout : State → Output
        update : State → Input → State

InitializedMooreMachine : {State Input Output : Set} →  Set
InitializedMooreMachine {State} {Input} {Output} = MooreMachine {State} {Input} {Output} × State 

-- A dynamical system lens (domain polynomial is selfMonomial) where the interface is a monomial is the same as a moore machine.
simpleLensIsMooreMachine : {State Input Output : Set} → Lens (selfMonomial State) (monomial Output Input) ≡ MooreMachine {State} {Input} {Output}
simpleLensIsMooreMachine {State} {Input} {Output} = isoToPath (iso go back (λ _ → refl) λ _ → refl)
    where
        go : Lens (selfMonomial State) (monomial Output Input) → MooreMachine {State} {Input} {Output}
        go (f ⇆ f♯) = mkMooreMachine f f♯

        back : MooreMachine {State} {Input} {Output} → Lens (selfMonomial State) (monomial Output Input)
        back (mkMooreMachine readout update) = readout ⇆ update

-- Having a lens from Y to selfMonomial S is the same thing as picking a state.
pickInitialState : {S : Set} → Lens Y (selfMonomial S) ≡ S
pickInitialState {S} = isoToPath (iso go back (λ _ → refl) λ _ → refl)
    where
        go : Lens Y (selfMonomial S) → S
        go (f ⇆ f♯) = f tt

        back : S → Lens Y (selfMonomial S)
        back s = (λ _ → s) ⇆ (λ _ _ → tt)

×≡ : {A B C D : Set} → (A ≡ B) → (C ≡ D) → (A × C) ≡ (B × D)
×≡ p1 p2 i = p1 i × p2 i

-- Therefore, an initialized moore machine consists of the two lenses: Y -> selfMonomial S -> monomial Output Input
initializedMooreMachineIsTwoLenses : {State Input Output : Set} → (Lens (selfMonomial State) (monomial Output Input) × Lens Y (selfMonomial State)) ≡ InitializedMooreMachine {State} {Input} {Output}
initializedMooreMachineIsTwoLenses = ×≡ simpleLensIsMooreMachine pickInitialState
