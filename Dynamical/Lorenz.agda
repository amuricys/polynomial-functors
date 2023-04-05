{-# OPTIONS --sized-types #-}


module Dynamical.Lorenz where

open import Codata.Stream
open import Dynamical.System
open import Data.Product
open import Data.Float renaming (Float to ℝ)
open import Common.CategoryData renaming (_*_ to _*p_ ; _+_ to _+p_) hiding (Y)
open import Data.Vec using (Vec ; map)
open import Data.Unit

dt : ℝ
dt = 0.01

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
x : DynamicalSystem
x = MkDynamicalSystem X (MkPoly X λ _ → Y) (readout ⇄ update)
  where readout : X → X
        readout state = state
        update : X → Y → X
        update (xnt state) (ynt y) = xnt (state + dt * (σ * (y - state)))

y : DynamicalSystem
y = MkDynamicalSystem Y (MkPoly Y λ _ → X × Z) (readout ⇄ update)
  where readout : Y → Y
        readout state = state
        update : Y → X × Z → Y
        update (ynt state) ( xnt x , znt z ) = ynt (state + dt * (x * (ρ - z) - state))

z : DynamicalSystem
z = MkDynamicalSystem Z (MkPoly Z λ _ → X × Y) (readout ⇄ update)
  where readout : Z → Z
        readout state = state
        update : Z → X × Y → Z
        update (znt state) (xnt x , ynt y) = znt (state + dt * (x * y - β * state))


preLorenz : DynamicalSystem
preLorenz = x &&& y &&& z

-- Wiring diagram is an arrow between monomials (lens)
lorenzWiringDiagram : Arrow (DynamicalSystem.interface preLorenz) (Emitter (X × Y × Z))
lorenzWiringDiagram = mp ⇄ md
  where mp : X × Y × Z → X × Y × Z
        mp (x , y , z) = x , y , z
        md : X × Y × Z → ⊤ → Y × (X × Z) × (X × Y)
        md (x , y , z) _ = y , (x , z) , (x , y)

-- Final system is composition of wiring diagram and dynamics
lorenz : DynamicalSystem
lorenz = install preLorenz (Emitter (X × Y × Z)) lorenzWiringDiagram

lorenzSeq : Stream (X × Y × Z) _
lorenzSeq = run lorenz auto (xnt 10.0 , ynt 10.0 , znt 10.0)

lorenzList : Vec (ℝ × ℝ × ℝ) 1000
lorenzList = Data.Vec.map (\{(xnt x , ynt y , znt z) → x , y , z } ) (take 1000 lorenzSeq)
