{-# OPTIONS --sized-types #-}


module Dynamical.LotkaVolterra where

open import Codata.Stream
open import Dynamical.System
open import Data.Product
open import Data.Float renaming (Float to ℚ) -- Rationals are more well behaved than reals (those are not even in stdlib)
open import Common.CategoryData renaming (_*_ to _*p_ ; _+_ to _+p_)
open import Data.Vec using (Vec)

dt : ℚ
dt = 0.1

-- First order differential equations
rabbits : DynamicalSystem
rabbits = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ × ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        update : ℚ → ℚ × ℚ → ℚ
        update state (birthRabbits , deathRabbits) = state + dt * (state  * (birthRabbits - deathRabbits))

foxes : DynamicalSystem
foxes = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ × ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        update : ℚ → ℚ × ℚ → ℚ
        update state (birthFoxes , deathFoxes) = state + dt * (state * (birthFoxes - deathFoxes))

preLV : DynamicalSystem
preLV = rabbits &&& foxes

-- Wiring diagram is an arrow between monomials (lens)
lotkaVolterraWiringDiagram : Arrow (DynamicalSystem.interface preLV) (selfMonomial (ℚ × ℚ))
lotkaVolterraWiringDiagram = (λ {(r , f) → r , f}) ⇄ (λ {(r , f) (a , b) → (a , c₂ * f) , (c₁ * r , b) })
  where c₁ = 0.4
        c₂ = 0.7

-- Final system is composition of wiring diagram and dynamics
lotkaVolterra : DynamicalSystem
lotkaVolterra = install preLV (selfMonomial (ℚ × ℚ)) lotkaVolterraWiringDiagram

lvSeq : Stream (ℚ × ℚ) _
lvSeq = run lotkaVolterra (constI (1.1 , 0.4)) (0.6 , 0.4)

lvList : Vec (ℚ × ℚ) 1000
lvList = take 1000 lvSeq
