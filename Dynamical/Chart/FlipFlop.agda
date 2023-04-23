{-# OPTIONS --cubical --two-level --sized-types --without-K --overlapping-instances #-}
module Dynamical.Chart.FlipFlop where

open import Dynamical.System
open import CategoryData.Everything
open import Agda.Builtin.Nat
open import Data.Unit
open import Data.Vec using (Vec)
open import Data.List hiding (take; _++_)
open import Codata.Stream
open import Codata.Thunk
open import Data.Nat.DivMod 
open import Data.Bool
open import Cubical.Foundations.Everything hiding (id; _∘_)
open import Function
open import Cubical.Chart.ChartLensCommute
open import CategoryData.Chart.Core

-- Example from https://www.youtube.com/watch?v=QNuGyjHJtP8, ~20 min mark

data Switch : Set where
    on : Switch
    off : Switch

toggle : Switch → Switch
toggle on = off
toggle off = on

-- | Commonly used where input to enclosed dynamical system where updateState only depends on current state.
ignoreUnitInput : {A B : Set} → (A → B) → A → ⊤ → B
ignoreUnitInput f a tt = f a

-- | Note: linear interface is used to accept only 1 possible input.
--   Readout defined as id to expose state.
flipFlop : DynamicalSystem
flipFlop = MkDynamicalSystem Switch (linear Switch) (id ⇆ ignoreUnitInput toggle)

-- | Result is: on, off, on, off...
flipFlopRan : Vec Switch 10
flipFlopRan = take 10 $ run flipFlop auto on

modNat : Nat → Switch
modNat n = if n % 2 == 0 then on else off

-- | To compare flipFlop and counter they need to have the same interface.
counter : DynamicalSystem
counter = MkDynamicalSystem Nat (linear Switch) (modNat ⇆ ignoreUnitInput suc)

-- | Result is: on, off, on, off...
counterRan : Vec Switch 10
counterRan = take 10 $ run counter auto 0

-- | Morphism between p dynamicalSystems with states Nat and Switch.
morphSystem : Nat → Switch
morphSystem = modNat

open DynamicalSystem
law₁ : let 
        r = mapPosition (dynamics counter)
        r' = mapPosition (dynamics flipFlop)
        f = morphSystem
    in  (n : Nat) → r' (f n)  ≡ r n
law₁ n = refl

-- law₂ : let 
--         u = mapDirection (dynamics counter)
--         u' = mapDirection (dynamics flipFlop)
--         f = morphSystem
--     in  (s : Nat) (x : ⊤) → {! u' ? ≡   !} -- u' (f s x) ≡ (f ∘ (u s)) x
law₂ : let 
        g# = mapDirection (dynamics counter)
        g = mapPosition (dynamics counter)
        h# = mapDirection (dynamics flipFlop)
        h = mapPosition (dynamics flipFlop)
        f = morphSystem
        p = linear Switch
    in  (s : Nat) (dir : (direction p) (g s)) → f (g# s dir) ≡ h# (f s) (subst (λ x → direction p x) (sym (law₁ s)) dir)
law₂ zero x = refl
law₂ (suc zero) x = refl
law₂ (suc (suc s)) x = law₂ s x

square : LensChartCommute (dynamics counter) (dynamics flipFlop) (morphSystem ⇉ λ _ → morphSystem) idChart
square = law₁ , law₂