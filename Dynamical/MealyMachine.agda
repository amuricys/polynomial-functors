{-# OPTIONS --without-K --sized-types #-}
 
module Dynamical.MealyMachine where

open import Data.Product
open import Codata.Stream
open import Data.Vec using (Vec ; reverse)
open import Codata.Thunk
open import Data.List using ([_])
open import Data.Product
open import Data.Nat using (ℕ)
open import Data.Float
open import CategoryData.Everything hiding (_*_ ; _+_)
record MealyMachine {State : Set} {Input : Set} {Output : Set} : Set where
    constructor mkmealy
    field
        run : State → Input → (State × Output)


-- go : {State Input Output : Set} → Lens (selfMonomial (State × Input)) (monomial Output Input) → MealyMachine {State} {Input} {Output}
-- go {State} {Input} {Output}  (readout ⇆ update) =
--   mkmealy runner 
--     where runner : State → Input → State × Output
--           runner oldState input = newState , output
--               where updated = update (oldState , input) input
--                     newState : State
--                     newState = proj₁ (update (oldState , input) input)
--                     output : Output
--                     output = readout (oldState , input)
-- back : {State Input Output : Set} → MealyMachine {State} {Input} {Output} → Lens (selfMonomial (State × Input)) (monomial Output Input)
-- back {State} {Input} {Output}  (mkmealy runner)  = readout ⇆ update
--    where readout : State × Input → Output
--          readout (state , input) = proj₂ (runner state input)
--          update : State × Input → Input → State × Input
--          update (state , oldInput) newInput = proj₁ (runner state oldInput) , newInput 

-- open MealyMachine
-- {-# TERMINATING #-}
-- exec : {State Input Output : Set} → (d : MealyMachine {State} {Input} {Output}) → State → Stream Input _ → Stream (State × Output) _
-- exec {State} {Input} {Output} d initialState inputs =  [ output ] ++ exec d (proj₁ output) (drop 1 inputs) --  [ output ] ++ (exec d e next)
--     where output : State × Output
--           output = run d initialState (head inputs)
-- {-# TERMINATING #-}
-- execLens : {State Input Output : Set} → Lens (selfMonomial (State × Input)) (monomial Output Input) → State → Stream Input _ → Stream Output _
-- execLens {State} {Input} {Output} l@(f ⇆ f♯) initialState inputs =  [ output ] ++ execLens l newState (drop 1 inputs)
--     where output : Output
--           output = f (initialState , head inputs)
--           newState : State
--           newState = proj₁ (f♯ (initialState , (head inputs)) (head inputs))

-- -- "0.5bej" Vec.∷
-- "0.01bej" Vec.∷
-- "0.02bej" Vec.∷
-- "0.04bej" Vec.∷
-- "0.08bej" Vec.∷
-- "0.061bej" Vec.∷
-- "0.023bej" Vec.∷
-- "0.046bej" Vec.∷ 
-- "0.0821bej" Vec.∷ 
-- -- "0.0652bej" Vec.∷ Vec.[]

-- open import Data.String
-- open import Function
-- mealyList : Vec (Float × String) 10
-- mealyList = take 10 (exec mealyform 5.0 (unfold (λ x → x + 1.0 , "jeb") 0.0))
--   where mealyform = (mkmealy (λ x x₁ → x * 2.0 , fromVec (reverse (toVec (x₁ Data.String.++ Data.Float.show x))))) 
--         lensform = back ∘ go ∘ back $ mealyform

  