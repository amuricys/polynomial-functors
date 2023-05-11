{-# OPTIONS --cubical --two-level --sized-types --without-K --overlapping-instances #-}

-- | Example taken from https://www.youtube.com/watch?v=QNuGyjHJtP8, ~ 30 min mark
module Dynamical.Chart.SimulateStateMachine where

open import Dynamical.System
open import CategoryData.Everything
open import Cubical.Foundations.Everything
open import Cubical.ChartLensCommute
open import CategoryData.Chart

data S : Set where
    one : S
    two : S
    three : S
    four : S
    five : S

data T : Set where
    one : T
    two : T
    three : T

data RedBlue : Set where
    red : RedBlue
    blue : RedBlue

data BrownOrange : Set where
    brown : BrownOrange
    orange : BrownOrange

data Output : Set where
    a : Output 
    b : Output
    c : Output
    d : Output

p : Polynomial
p = mkpoly Output λ {a → RedBlue
                           ; b → RedBlue
                           ; c → BrownOrange
                           ; d → BrownOrange}
                            
bigLens : Lens (selfMonomial S) p
bigLens = output ⇆ input
    where 
        output : S → Output
        output one = a
        output two = a
        output three = b
        output four = d
        output five = d

        -- The transition table
        input : (s : S) → direction p (output s) → direction (selfMonomial S) s
        input one red = three
        input one blue = one
        input two red = three
        input two blue = two
        input three red = four
        input three blue = five
        input four brown = four
        input four orange = one
        input five brown = five
        input five orange = two

bigSystem : DynamicalSystem
bigSystem = MkDynamicalSystem S p bigLens

smallLens : Lens (selfMonomial T) p
smallLens = output ⇆ input
    where
        output : T → Output
        output one = a
        output two = b
        output three = d

        input : (t : T) → direction p (output t) → direction (selfMonomial T) t
        input one red = two
        input one blue = one
        input two red = three
        input two blue = three
        input three brown = three
        input three orange = one

-- | More compact version of big system with same semantics
smallSystem : DynamicalSystem
smallSystem = MkDynamicalSystem T p smallLens


morphSystem : S → T
morphSystem one = one
morphSystem two = one
morphSystem three = two
morphSystem four = three
morphSystem five = three

open DynamicalSystem
law₁ : let 
        g# = mapDirection (dynamics bigSystem)
        g = mapPosition (dynamics bigSystem)
        h# = mapDirection (dynamics smallSystem)
        h = mapPosition (dynamics smallSystem)
        f = morphSystem
    in  (s : S) → h (f s) ≡ g s
law₁ one = refl
law₁ two = refl
law₁ three = refl
law₁ four = refl
law₁ five = refl 

law₂ : let 
        g# = mapDirection (dynamics bigSystem)
        g = mapPosition (dynamics bigSystem)
        h# = mapDirection (dynamics smallSystem)
        h = mapPosition (dynamics smallSystem)
        f = morphSystem
    in  (s : S) (dir : (direction p) (g s)) → f (g# s dir) ≡ h# (f s) (subst (λ x → direction p x) (sym (law₁ s)) dir)
law₂ one red = refl
law₂ one blue = refl
law₂ two red = refl
law₂ two blue = refl
law₂ three red = refl
law₂ three blue = refl
law₂ four brown = refl
law₂ four orange = refl
law₂ five brown = refl
law₂ five orange = refl

square : LensChartCommute bigLens smallLens (morphSystem ⇉ λ _ → morphSystem) idChart
square = law₁ , law₂