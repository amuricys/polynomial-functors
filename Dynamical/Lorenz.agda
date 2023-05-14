{-# OPTIONS --sized-types #-}


module Dynamical.Lorenz where

open import Codata.Stream
open import Dynamical.System
open import Data.Product
open import Data.Float renaming (Float to ℝ)
open import CategoryData.Everything renaming (_*_ to _*p_ ; _+_ to _+p_ ; Y to Y')
open import Data.Vec using (Vec ; map)
open import Data.Unit

σ = 10.0
ρ = 28.0
β = 8.0 ÷ 3.0

data X : Set where
  xnt : ℝ → X

data Y : Set where
  ynt : ℝ → Y

data Z : Set where
  znt : ℝ → Z

-- First order differential equations
x : ℝ → DynamicalSystem
x dt = mkdyn X (mkpoly X λ _ → Y) (readout ⇆ update)
  where readout : X → X
        readout state = state
        update : X → Y → X
        update (xnt state) (ynt y) = xnt (state + dt * (σ * (y - state)))

y : ℝ → DynamicalSystem
y dt = mkdyn Y (mkpoly Y λ _ → X × Z) (readout ⇆ update)
  where readout : Y → Y
        readout state = state
        update : Y → X × Z → Y
        update (ynt state) ( xnt x , znt z ) = ynt (state + dt * (x * (ρ - z) - state))

z : ℝ → DynamicalSystem
z dt = mkdyn Z (mkpoly Z λ _ → X × Y) (readout ⇆ update)
  where readout : Z → Z
        readout state = state
        update : Z → X × Y → Z
        update (znt state) (xnt x , ynt y) = znt (state + dt * (x * y - β * state))


preLorenz : ℝ → DynamicalSystem
preLorenz dt = x dt &&& y dt &&& z dt

-- Wiring diagram is an lens between monomials (lens)
lorenzWiringDiagram : Lens (DynamicalSystem.interface (preLorenz 0.0 {- we just want the interface -})) (emitter (X × Y × Z))
lorenzWiringDiagram = mp ⇆ md
  where mp : X × Y × Z → X × Y × Z
        mp (x , y , z) = x , y , z
        md : X × Y × Z → ⊤ → Y × (X × Z) × (X × Y)
        md (x , y , z) _ = y , (x , z) , (x , y)

-- Final system is composition of wiring diagram and dynamics
lorenz : ℝ → DynamicalSystem
lorenz dt = install (preLorenz dt) (emitter (X × Y × Z)) lorenzWiringDiagram

lorenzSeq : ℝ → ℝ → ℝ → ℝ → Stream (X × Y × Z) _
lorenzSeq x0 y0 z0 dt = run (lorenz dt) auto (xnt x0 , ynt y0 , znt z0)

lorenzList : ℝ → ℝ → ℝ → ℝ → Vec (ℝ × ℝ × ℝ) 1000
lorenzList x0 y0 z0 dt = Data.Vec.map (\{(xnt x , ynt y , znt z) → x , y , z } ) (take 1000 (lorenzSeq x0 y0 z0 dt))

outToVec : X × Y × Z → Vec ℝ 3
outToVec (xnt x , ynt y , znt z) = (x Vec.∷ y Vec.∷ z Vec.∷ Vec.[])