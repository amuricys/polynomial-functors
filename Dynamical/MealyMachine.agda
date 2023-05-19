{-# OPTIONS --without-K --sized-types #-}
 
module Dynamical.MealyMachine where

open import Data.Product
open import Codata.Stream
open import Codata.Thunk
open import Data.List hiding (_++_ ; drop ; head)
open import Data.Product
open import Data.Nat

record MealyMachine {State : Set} {Input : Set} {Output : Set} : Set where
    constructor mkmealy
    field
        run : State → Input → (State × Output)
open MealyMachine
{-# TERMINATING #-}
exec : {State Input Output : Set} → (d : MealyMachine {State} {Input} {Output}) → State → Stream Input _ → Stream (State × Output) _
exec {State} {Input} {Output} d initialState inputs =  [ output ] ++ exec d (proj₁ output) (drop 1 inputs) --  [ output ] ++ (exec d e next)
    where output : State × Output
          output = run d initialState (head inputs)
