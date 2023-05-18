{-# OPTIONS --without-K #-}
 
module Dynamical.MealyMachine where

open import Data.Product

record MealyMachine : Set₁ where
    constructor MkMealyMachine
    field
        State : Set
        Input : Set
        Output : Set
        run : State → Input → (State × Output)


open MealyMachine

record InitializedMealyMachine : Set₁ where
    field
        mealyMachine : MealyMachine
        initialState : State mealyMachine