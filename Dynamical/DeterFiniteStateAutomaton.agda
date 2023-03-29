{-# OPTIONS --without-K #-}

module Dynamical.DeterFiniteStateAutomaton where

open import Data.Bool

record DFS {State Alphabet : Set} : Set where
    constructor MkDFS
    field
        initial : State
        update : State → Alphabet → State
        -- Partitions all states into recognized and unrecognized states.
        recognized : State → Bool



