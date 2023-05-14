{-# OPTIONS --sized-types #-}


module Dynamical.HodgkinHuxley where

open import Codata.Stream
open import Dynamical.System
open import Data.Product
open import Data.Float renaming (Float to ℝ)
open import CategoryData.Everything renaming (_*_ to _*p_ ; _+_ to _+p_)
open import CategoryData.SimplePolynomials using (selfMonomial)
open import Data.Vec using (Vec)

-- https://mark-kramer.github.io/Case-Studies-Python/HH.html

dt : ℝ
dt = 0.01

e : ℝ
e = 2.718281

open DynamicalSystem

-- The big one
voltage : ℝ → DynamicalSystem
voltage dt = mkdyn ℝ (mkpoly ℝ λ _ → ℝ × ℝ × ℝ × ℝ) (readout ⇆ update)
  where readout : ℝ → ℝ
        readout state = state
        GL : ℝ
        GL = 0.3
        EL : ℝ
        EL = 10.6
        Gna : ℝ
        Gna = 120.0
        Ena : ℝ
        Ena = 115.0
        Gk : ℝ
        Gk = 36.0
        Ek : ℝ
        Ek = -12.0
        update : ℝ → ℝ × ℝ × ℝ × ℝ → ℝ
        update state (Ie , m , h , n) = state + dt * dv
            where v = state + 65.0
                  dv  = Gna * m ** 3.0 * h * (Ena - v) + Gk * n ** 4.0 * (Ek - v) + GL * (EL - v) + Ie
                  -- V[i+1] = gNa0*m[i]**3*h[i]*(ENa-(V[i]+65)) + gK0*n[i]**4*(EK-(V[i]+65)) + gL0*(EL-(V[i]+65)) + I0
                   -- dv = (- GL * (state - EL) - Gna * m ** 3.0 * h * (state - Ena) - Gk * n ** 4.0 * (state - Ek) + Ie ) 
-- Helper functions -----
αₘ : ℝ → ℝ
--           (2.5 - 0.1 * (V+65))           / (np.exp(2.5-0.1 * (V        + 65))    -1)
αₘ voltage = (2.5 - 0.1 * (voltage + 65.0)) ÷ (e ** (2.5 - 0.1 * (voltage + 65.0)) - 1.0)
βₘ : ℝ → ℝ
--           4   * np.exp(-(V+65)/18)
βₘ voltage = 4.0 * e ** (-(voltage + 65.0) ÷ 18.0)

αₕ : ℝ → ℝ
--           0.07 * np.exp(-(V+65)/20)
αₕ voltage = 0.07 * e ** (-(voltage + 65.0) ÷ 20.0)
βₕ : ℝ → ℝ
-- 1/(np.exp(3.0-0.1*(V+65))+1)
βₕ voltage = 1.0 ÷ (1.0 + e ** (3.0 - 0.1 * (voltage + 65.0)) )

αₙ : ℝ → ℝ
--          (0.1-0.01*(V+65))        / (np.exp(1-0.1*(V+65)) -1)
αₙ voltage = (0.1 - 0.01 * (voltage + 65.0)) ÷ (e ** (1.0 - 0.1 * (voltage + 65.0)) - 1.0)
βₙ : ℝ → ℝ
--           0.125 * np.exp(-(V+65)/80)
βₙ voltage = 0.125 * e ** ((voltage + 65.0) ÷ 80.0)
-------------------------

-- First order differential equations
potassiumActivation :  ℝ → DynamicalSystem
potassiumActivation dt = mkdyn ℝ (mkpoly ℝ λ _ → ℝ) (readout ⇆ update)
  where readout : ℝ → ℝ
        readout state = state
        update : ℝ → ℝ → ℝ
        update state voltage = state + dt * dₘ
          where dₘ = αₘ voltage * (1.0 - state) - βₘ voltage * state

sodiumActivation : ℝ → DynamicalSystem
sodiumActivation dt = mkdyn ℝ (mkpoly ℝ λ _ → ℝ) (readout ⇆ update)
  where readout : ℝ → ℝ
        readout state = state
        update : ℝ → ℝ → ℝ
        update state voltage = state + dt * dₕ
          where dₕ = αₕ voltage * (1.0 - state) - βₕ voltage * state

sodiumInactivation : ℝ → DynamicalSystem
sodiumInactivation dt = mkdyn ℝ (mkpoly ℝ λ _ → ℝ) (readout ⇆ update)
  where readout : ℝ → ℝ
        readout state = state
        update : ℝ → ℝ → ℝ
        update state voltage = state + dt * dₙ
          where dₙ = αₙ voltage * (1.0 - state) - βₙ voltage * state   

preHH : ℝ → DynamicalSystem
preHH dt = voltage dt &&& potassiumActivation dt &&& sodiumActivation dt &&& sodiumInactivation dt

hodgkinHuxleyWiringDiagram : Lens (interface (preHH 0.0)) (selfMonomial ℝ)
hodgkinHuxleyWiringDiagram = (λ {(v , m , h , n) → v }) ⇆ (λ {((v , m , h , n)) Ie → (Ie , m , h , n) , v , v , v })

hodgkinHuxley : ℝ → DynamicalSystem
hodgkinHuxley dt = install (preHH dt) (selfMonomial ℝ) hodgkinHuxleyWiringDiagram

preHHWithInput : ℝ → DynamicalSystem
preHHWithInput dt = hodgkinHuxley dt &&& functionToDynamicalSystem ℝ ℝ λ x → x + (dt * 0.02)

hhWithInputWiring : Lens (interface (preHHWithInput 0.0)) (emitter ℝ)
hhWithInputWiring = (λ { (hhOut , _) → hhOut}) ⇆ λ { (hhOut , fnOut) _ → fnOut , fnOut }

hhWithInput : ℝ → DynamicalSystem
hhWithInput dt = install (preHHWithInput dt) (emitter ℝ) hhWithInputWiring

hhSeqWithInput : ℝ → Stream ℝ _
hhSeqWithInput dt = run (hhWithInput dt) auto ((V₀ , m∞ , n∞ , h∞) , -5.0)
  where V₀ : ℝ
        V₀ = -70.0
        m∞ : ℝ
        m∞ = 0.05
        n∞ : ℝ
        n∞ = 0.54
        h∞ : ℝ
        h∞ = 0.34

hhSeq : ℝ → Stream ℝ _
hhSeq dt = run (hodgkinHuxley dt) (constI Ie) (V₀ , m∞ , n∞ , h∞)
  where V₀ : ℝ
        V₀ = -70.0
        m∞ : ℝ
        m∞ = 0.05
        n∞ : ℝ
        n∞ = 0.54
        h∞ : ℝ
        h∞ = 0.34
        Ie : ℝ
        Ie = 10.0


hhList : ℝ → Vec ℝ 15000
hhList dt = take 15000 (hhSeqWithInput dt)

