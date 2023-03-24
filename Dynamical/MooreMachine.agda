{-# OPTIONS --without-K #-}
 
module Dynamical.MooreMachine where

record MooreMachine : Set₁ where
    constructor MkMooreMachine
    field
        State : Set
        Input : Set
        Output : Set
        update : State → Input → State
        readout : State → Output

open MooreMachine

record InitializedMooreMachine : Set₁ where
    field
        mooreMachine : MooreMachine
        initialState : State mooreMachine