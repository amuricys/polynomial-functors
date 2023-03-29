{-# OPTIONS --cubical #-}

module Cubical.ArrowIsDFS where

open import Dynamical.DeterFiniteStateAutomaton
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Common.CategoryData
open import Data.Bool
open import Data.Product
open import Data.Unit

-- Explained at day 3, around 20 minute mark: https://www.youtube.com/watch?v=pRN4e5YS90I.
arrowIsDFS : {State Alphabet : Set} → DFS {State} {Alphabet} ≡ (Arrow (selfMonomial State) (monomial Bool Alphabet) × Arrow Y (selfMonomial State))
arrowIsDFS {State} {Alphabet} = isoToPath (iso fromDfs toDfs (λ x → refl) λ a → refl) 
    where
        fromDfs : DFS {State} {Alphabet} → (Arrow (selfMonomial State) (monomial Bool Alphabet) × Arrow Y (selfMonomial State))
        fromDfs (MkDFS initial update recognized) 
            = (recognized ⇄ update) , ((λ x → initial) ⇄ λ fromPos x → fromPos)

        toDfs : Arrow (selfMonomial State) (monomial Bool Alphabet) × Arrow Y (selfMonomial State) → DFS {State} {Alphabet}
        toDfs ((mapPosition ⇄ mapDirection) , initState) 
            = MkDFS (Arrow.mapPosition initState tt) mapDirection mapPosition

