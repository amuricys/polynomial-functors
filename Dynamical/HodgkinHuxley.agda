{-# OPTIONS --sized-types #-}


module Dynamical.HodgkinHuxley where

open import Codata.Stream
open import Dynamical.System
open import Data.Product
open import Data.Float renaming (Float to ℚ) -- Rationals are more well behaved than reals (those are not even in stdlib)
open import Common.CategoryData renaming (_*_ to _*p_ ; _+_ to _+p_) hiding (C)
open import Data.Vec using (Vec)

-- https://www.chegg.com/homework-help/questions-and-answers/box-1-hodgkin-huxley-model-main-equations-cox-g-v-v-gnam-h-v-ena-gkn-v-ek-le-13-dit-v-memb-q46967162

-- C dV/dt = -GL(V - VL) - Gna * m³h*(V - Ena) - Gk * n**4(V - Ek) + Ie
--   dm/dt = αₘ(V)(1 - m) - βₘ(V)m
--   dh/dt = αₕ(V)(1 - h) - βₕ(V)h
--   dn/dt = αₙ(V)(1 - n) - βₙ(V)n
-- and then a ton of literals lol

dt : ℚ
dt = 0.1

e : ℚ
e = 2.7

-- The big one
voltage : DynamicalSystem
voltage = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ × ℚ × ℚ × ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        GL : ℚ
        GL = 2.0
        C : ℚ
        C = 2.0
        VL : ℚ
        VL = - 65.0
        Gna : ℚ
        Gna = 400.0
        Ena : ℚ
        Ena = 99.0
        Gk : ℚ
        Gk = 200.0
        Ek : ℚ
        Ek = - 85.0
        update : ℚ → ℚ × ℚ × ℚ × ℚ → ℚ
        update state (Ie , m , n , h) = (- GL * (state - VL) - Gna * m ** 3.0 * h * (state - Ena) - Gk * n ** 4.0 * (state - Ek) + Ie ) ÷ C

-- Helper functions -----
αₘ : ℚ → ℚ
αₘ voltage = 0.1 * (voltage + 40.0) ÷ (1.0 - e ** (-0.1 * (voltage + 40.0)))
βₘ : ℚ → ℚ
βₘ voltage = 4.0 * e ** (- 0.056 * (voltage + 65.0))

αₕ : ℚ → ℚ
αₕ voltage = 0.07 * e ** (-0.05 * (voltage + 65.0))
βₕ : ℚ → ℚ
βₕ voltage = 1.0 ÷ (1.0 + e ** (-0.1 * (voltage + 35.0)) )

αₙ : ℚ → ℚ
αₙ voltage = 0.01 * (voltage + 55.0) ÷ (1.0 - e ** (-0.1 * (voltage + 55.0)))
βₙ : ℚ → ℚ
βₙ voltage = 0.125 * e ** (-0.0125 * (voltage + 65.0))
-------------------------

-- First order differential equations
potassiumActivation : DynamicalSystem
potassiumActivation = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ × ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        update : ℚ → ℚ × ℚ → ℚ
        update state (voltage , probability) = state + dt * αₘ voltage * (1.0 - probability) - βₘ voltage * probability

sodiumActivation : DynamicalSystem
sodiumActivation = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ × ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        update : ℚ → ℚ × ℚ → ℚ
        update state (voltage , probability) = state + dt * αₕ voltage * (1.0 - probability) - βₕ voltage * probability

sodiumInactivation : DynamicalSystem
sodiumInactivation = MkDynamicalSystem ℚ (MkPolynomial ℚ λ _ → ℚ × ℚ) (readout ⇄ update)
  where readout : ℚ → ℚ
        readout state = state
        update : ℚ → ℚ × ℚ → ℚ
        update state (voltage , probability) = state + dt * αₙ voltage * (1.0 - probability) - βₙ voltage * probability   

preHH : DynamicalSystem
preHH = voltage &&& potassiumActivation &&& sodiumActivation &&& sodiumInactivation

-- Wiring diagram is an arrow between monomials (lens)
-- This is definitely wrong. bears writing the wiring diagram out to see what goes where
hodgkinHuxleyWiringDiagram : Arrow (DynamicalSystem.interface preHH) (selfMonomial (ℚ × ℚ × ℚ × ℚ))
hodgkinHuxleyWiringDiagram = (λ {(v , m , n , h) → v , m , n , h}) ⇄ (λ {((v , m , n , h)) (a , b , c , d) → (d , d , d , d) , (d , d) , (d , d) , d , d })

-- Final system is composition of wiring diagram and dynamics
hodgkinHuxley : DynamicalSystem
hodgkinHuxley = install preHH (selfMonomial (ℚ × ℚ × ℚ × ℚ)) hodgkinHuxleyWiringDiagram

hhSeq : Stream (ℚ × ℚ × ℚ × ℚ) _
hhSeq = run hodgkinHuxley (constI (V₀ , m∞ V₀ , n∞ V₀ , h∞ V₀)) (V₀ , m∞ V₀ , n∞ V₀ , h∞ V₀)
  where V₀ : ℚ
        V₀ = -65.0
        m∞ : ℚ → ℚ
        m∞ v = αₘ v ÷ (αₘ v + βₘ v)
        n∞ : ℚ → ℚ
        n∞ v = αₙ v ÷ (αₙ v + βₙ v)
        h∞ : ℚ → ℚ
        h∞ v = αₙ v ÷ (αₙ v + βₙ v)

hhList : Vec (ℚ × ℚ × ℚ × ℚ) 100
hhList = take 100 hhSeq
  