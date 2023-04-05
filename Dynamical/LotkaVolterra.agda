{-# OPTIONS --sized-types #-}


module Dynamical.LotkaVolterra where

open import Codata.Stream
open import Dynamical.System
open import Data.Product
open import Data.Float renaming (Float to ℝ)
open import Common.CategoryData renaming (_*_ to _*p_ ; _+_ to _+p_)
open import Data.Vec using (Vec)

dt : ℝ
dt = 0.1

-- First order differential equations
rabbits : DynamicalSystem
rabbits = MkDynamicalSystem ℝ (MkPoly ℝ λ _ → ℝ × ℝ) (readout ⇄ update)
  where readout : ℝ → ℝ
        readout state = state
        update : ℝ → ℝ × ℝ → ℝ
        update state (birthRabbits , deathRabbits) = state + dt * (state  * (birthRabbits - deathRabbits))

foxes : DynamicalSystem
foxes = MkDynamicalSystem ℝ (MkPoly ℝ λ _ → ℝ × ℝ) (readout ⇄ update)
  where readout : ℝ → ℝ
        readout state = state
        update : ℝ → ℝ × ℝ → ℝ
        update state (birthFoxes , deathFoxes) = state + dt * (state * (birthFoxes - deathFoxes))

preLV : DynamicalSystem
preLV = rabbits &&& foxes

-- Wiring diagram is an arrow between monomials (lens)
lotkaVolterraWiringDiagram : Arrow (DynamicalSystem.interface preLV) (selfMonomial (ℝ × ℝ))
lotkaVolterraWiringDiagram = (λ {(r , f) → r , f}) ⇄ (λ {(r , f) (a , b) → (a , c₂ * f) , (c₁ * r , b) })
  where c₁ = 0.4
        c₂ = 0.7

-- Final system is composition of wiring diagram and dynamics
lotkaVolterra : DynamicalSystem
lotkaVolterra = install preLV (selfMonomial (ℝ × ℝ)) lotkaVolterraWiringDiagram

lvSeq : Stream (ℝ × ℝ) _
lvSeq = run lotkaVolterra (constI (1.1 , 0.4)) (0.6 , 0.4)

lvList : Vec (ℝ × ℝ) 1000
lvList = take 1000 lvSeq
