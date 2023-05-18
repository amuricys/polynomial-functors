{-# OPTIONS --cubical #-}

module Cubical.LensIsDFS where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import CategoryData.Everything
open import Data.Bool
open import Data.Product
open import Data.Unit
open import Cubical.LensIsMooreMachine


-- Deterministic finite state automata
record DFS {State Alphabet : Set} : Set where
    constructor mkDFS
    field
        -- Partitions all states into recognized and unrecognized states.
        recognized : State → Bool
        update : State → Alphabet → State

InitializedDFS : {State Alphabet : Set} → Set
InitializedDFS {State} {Alphabet} = DFS {State} {Alphabet} × State

-- Explained at day 3, around 20 minute mark: https://www.youtube.com/watch?v=pRN4e5YS90I.
-- Output of lens is Bool (partioning), and input is always alphabet
lensIsDFS : {State Alphabet : Set} → DFS {State} {Alphabet} ≡ Lens (selfMonomial State) (monomial Bool Alphabet)
lensIsDFS {State} {Alphabet} = isoToPath (iso go back (λ _ → refl) (λ _ → refl)) 
    where
        go : DFS {State} {Alphabet} → Lens (selfMonomial State) (monomial Bool Alphabet)
        go (mkDFS recognized update) = recognized ⇆ update

        back : Lens (selfMonomial State) (monomial Bool Alphabet) → DFS {State} {Alphabet}
        back (f ⇆ f♯) = mkDFS f f♯

initializedDfsIsTwoLenses : {State Alphabet : Set} → (Lens (selfMonomial State) (monomial Bool Alphabet) × Lens Y (selfMonomial State)) ≡ InitializedDFS {State} {Alphabet} 
initializedDfsIsTwoLenses = ×≡ (sym lensIsDFS) pickInitialState


-- Alternative proof: DFS is special moore machine which is lens, therefore DFS is a lens
dfsIsMooreMachine : {State Alphabet : Set} → DFS {State} {Alphabet} ≡ MooreMachine {State} {Alphabet} {Bool}
dfsIsMooreMachine {State} {Alphabet} = isoToPath (iso go back (λ _ → refl) (λ _ → refl))
    where
        go : DFS {State} {Alphabet} → MooreMachine {State} {Alphabet} {Bool}
        go (mkDFS recognized update) = mkMooreMachine recognized update

        back : MooreMachine {State} {Alphabet} {Bool} → DFS {State} {Alphabet}
        back (mkMooreMachine readout update) = mkDFS readout update

altLensIsDfs : {State Alphabet : Set} → DFS {State} {Alphabet} ≡ Lens (selfMonomial State) (monomial Bool Alphabet)
altLensIsDfs = sym (simpleLensIsMooreMachine ∙ (sym dfsIsMooreMachine))

