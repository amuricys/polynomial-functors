{-# OPTIONS --sized-types #-}


module Dynamical.LotkaVolterra where

open import Codata.Stream
open import Dynamical.System
open import Data.Product
open import Data.Float renaming (Float to ℝ)
open import CategoryData.Everything renaming (_*_ to _*p_ ; _+_ to _+p_)
open import Data.Vec using (Vec)
open import CategoryData.SimplePolynomials using (selfMonomial)

dt : ℝ
dt = 0.1

-- First order differential equations
rabbits : DynamicalSystem
rabbits = MkDynamicalSystem ℝ (mkpoly ℝ λ _ → ℝ × ℝ) (readout ⇆ update)
  where readout : ℝ → ℝ
        readout state = state
        update : ℝ → ℝ × ℝ → ℝ
        update state (birthRabbits , deathRabbits) = state + dt * (state  * (birthRabbits - deathRabbits))

foxes : DynamicalSystem
foxes = MkDynamicalSystem ℝ (mkpoly ℝ λ _ → ℝ × ℝ) (readout ⇆ update)
  where readout : ℝ → ℝ
        readout state = state
        update : ℝ → ℝ × ℝ → ℝ
        update state (birthFoxes , deathFoxes) = state + dt * (state * (birthFoxes - deathFoxes))

preLV : DynamicalSystem
preLV = rabbits &&& foxes

-- Wiring diagram is an lens between monomials (lens)
lotkaVolterraWiringDiagram : ℝ → ℝ → Lens (DynamicalSystem.interface preLV) (selfMonomial (ℝ × ℝ))
lotkaVolterraWiringDiagram foxPerCapDeath foxBloodthirst = outerOutput ⇆ innerInput
  where outerOutput : ℝ × ℝ → ℝ × ℝ
        outerOutput (rabbitOutput , foxOutput) = rabbitOutput , foxOutput
        innerInput : (outputs : ℝ × ℝ) → direction (selfMonomial (ℝ × ℝ)) (outerOutput outputs) → direction (DynamicalSystem.interface preLV) outputs
        innerInput (r , f) (rabMaxPerCapGrowth , howNutritiousRabbitsAre) = (rabMaxPerCapGrowth , foxBloodthirst * f) , (foxPerCapDeath * r , howNutritiousRabbitsAre)
        

-- Final system is composition of wiring diagram and dynamics
lotkaVolterra : ℝ → ℝ → DynamicalSystem
lotkaVolterra β γ = install preLV (selfMonomial (ℝ × ℝ)) (lotkaVolterraWiringDiagram β γ)

lvSeq : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Stream (ℝ × ℝ) _
lvSeq α β γ δ r0 f0 = run (lotkaVolterra β γ) (constI (α , δ)) (r0 , f0)

lvList : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → Vec (ℝ × ℝ) 1000
lvList α β γ δ r0 f0 = take 1000 (lvSeq α β γ δ  r0 f0)
