{-# OPTIONS --cubical #-}

module Cubical.LensIsDFS where

open import Dynamical.DeterFiniteStateAutomaton
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import CategoryData.Everything
open import Data.Bool
open import Data.Product
open import Data.Unit

-- Explained at day 3, around 20 minute mark: https://www.youtube.com/watch?v=pRN4e5YS90I.
lensIsDFS : {State Alphabet : Set} → DFS {State} {Alphabet} ≡ (Lens (selfMonomial State) (monomial Bool Alphabet) × Lens Y (selfMonomial State))
lensIsDFS {State} {Alphabet} = isoToPath (iso fromDfs toDfs (λ x → refl) λ a → refl) 
    where
        fromDfs : DFS {State} {Alphabet} → (Lens (selfMonomial State) (monomial Bool Alphabet) × Lens Y (selfMonomial State))
        fromDfs (MkDFS initial update recognized) 
            = (recognized ⇆ update) , ((λ x → initial) ⇆ λ fromPos x → fromPos)

        toDfs : Lens (selfMonomial State) (monomial Bool Alphabet) × Lens Y (selfMonomial State) → DFS {State} {Alphabet}
        toDfs ((mapPosition ⇆ mapDirection) , initState) 
            = MkDFS (Lens.mapPosition initState tt) mapDirection mapPosition

