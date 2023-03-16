{-# OPTIONS --sized-types #-}


module Dynamical.HodgkinHuxley where

open import Codata.Stream
open import Dynamical.System
open import Data.Product
open import Data.Float renaming (Float to ℚ) -- Rationals are more well behaved than reals (those are not even in stdlib)
open import Common.CategoryData renaming (_*_ to _*p_ ; _+_ to _+p_) hiding (C)
open import Data.Vec using (Vec)

-- https://mark-kramer.github.io/Case-Studies-Python/HH.html

dt : ℚ
dt = 0.01

e : ℚ
e = 2.718281

-- The big one
voltage : DynamicalSystem
voltage = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ × ℚ × ℚ × ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        GL : ℚ
        GL = 0.3
        EL : ℚ
        EL = 10.6
        Gna : ℚ
        Gna = 120.0
        Ena : ℚ
        Ena = 115.0
        Gk : ℚ
        Gk = 36.0
        Ek : ℚ
        Ek = -12.0
        update : ℚ → ℚ × ℚ × ℚ × ℚ → ℚ
        update state (Ie , m , h , n) = state + dt * dv
            where v = state + 65.0
                  dv  = Gna * m ** 3.0 * h * (Ena - v) + Gk * n ** 4.0 * (Ek - v) + GL * (EL - v) + Ie
                  -- V[i+1] = gNa0*m[i]**3*h[i]*(ENa-(V[i]+65)) + gK0*n[i]**4*(EK-(V[i]+65)) + gL0*(EL-(V[i]+65)) + I0
                   -- dv = (- GL * (state - EL) - Gna * m ** 3.0 * h * (state - Ena) - Gk * n ** 4.0 * (state - Ek) + Ie ) ÷ C

-- Helper functions -----
αₘ : ℚ → ℚ
--           (2.5 - 0.1 * (V+65))           / (np.exp(2.5-0.1 * (V        + 65))    -1)
αₘ voltage = (2.5 - 0.1 * (voltage + 65.0)) ÷ (e ** (2.5 - 0.1 * (voltage + 65.0)) - 1.0)
βₘ : ℚ → ℚ
--           4   * np.exp(-(V+65)/18)
βₘ voltage = 4.0 * e ** (-(voltage + 65.0) ÷ 18.0)

αₕ : ℚ → ℚ
--           0.07 * np.exp(-(V+65)/20)
αₕ voltage = 0.07 * e ** (-(voltage + 65.0) ÷ 20.0)
βₕ : ℚ → ℚ
-- 1/(np.exp(3.0-0.1*(V+65))+1)
βₕ voltage = 1.0 ÷ (1.0 + e ** (3.0 - 0.1 * (voltage + 65.0)) )

αₙ : ℚ → ℚ
--          (0.1-0.01*(V+65))        / (np.exp(1-0.1*(V+65)) -1)
αₙ voltage = (0.1 - 0.01 * (voltage + 65.0)) ÷ (e ** (1.0 - 0.1 * (voltage + 65.0)) - 1.0)
βₙ : ℚ → ℚ
--           0.125 * np.exp(-(V+65)/80)
βₙ voltage = 0.125 * e ** ((voltage + 65.0) ÷ 80.0)
-------------------------

-- First order differential equations
potassiumActivation : DynamicalSystem
potassiumActivation = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        update : ℚ → ℚ → ℚ
        update state voltage = state + dt * dₘ
          where dₘ = αₘ voltage * (1.0 - state) - βₘ voltage * state

sodiumActivation : DynamicalSystem
sodiumActivation = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        update : ℚ → ℚ → ℚ
        update state voltage = state + dt * dₕ
          where dₕ = αₕ voltage * (1.0 - state) - βₕ voltage * state

sodiumInactivation : DynamicalSystem
sodiumInactivation = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        update : ℚ → ℚ → ℚ
        update state voltage = state + dt * dₙ
          where dₙ = αₙ voltage * (1.0 - state) - βₙ voltage * state   

preHH : DynamicalSystem
preHH = voltage &&& potassiumActivation &&& sodiumActivation &&& sodiumInactivation

-- Wiring diagram is an arrow between monomials (lens)
-- The first function in the arrow simply selects something to be the output of the larger system.
-- The second one deals with wiring inputs. It has access to all outputs plus Ie, which is an input to
-- the outer box. Wonder why the first arrow doesn't have access to Ie though.
hodgkinHuxleyWiringDiagram : Arrow (DynamicalSystem.interface preHH) (selfMonomial ℚ)
hodgkinHuxleyWiringDiagram = (λ {(v , m , h , n) → v }) ⇄ (λ {((v , m , h , n)) Ie → (Ie , m , h , n) , v , v , v })

-- Final system is composition of wiring diagram and dynamics
hodgkinHuxley : DynamicalSystem
hodgkinHuxley = install preHH (selfMonomial ℚ) hodgkinHuxleyWiringDiagram

hhSeq : Stream ℚ _
hhSeq = run hodgkinHuxley (constI Ie) (V₀ , m∞ V₀ , n∞ V₀ , h∞ V₀)
  where V₀ : ℚ
        V₀ = -70.0
        m∞ : ℚ → ℚ
        m∞ v = 0.05 -- αₘ v ÷ (αₘ v + βₘ v)
        n∞ : ℚ → ℚ
        n∞ v = 0.54 -- αₙ v ÷ (αₙ v + βₙ v)
        h∞ : ℚ → ℚ
        h∞ v = 0.34 -- αₙ v ÷ (αₙ v + βₙ v)
        Ie : ℚ
        Ie = 10.0

hhList : Vec ℚ 2000
hhList = take 2000 hhSeq
