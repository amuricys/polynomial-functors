{-# OPTIONS --sized-types #-}

module Dynamical.System where

open import Agda.Builtin.Nat renaming (_+_ to _+ℕ_)
open import Common.CategoryData
open import Codata.Stream
open import Codata.Thunk
open import Data.List hiding (take; _++_)
open import Data.Vec using (Vec)
import Agda.Builtin.Nat
open import Function using (id)
open import Data.Product
open import Data.Unit

-- Creating dynamical systems.
record DynamicalSystem : Set₁ where
    constructor MkDynamicalSystem
    field
        state : Set -- S
        interface : Polynomial -- p
        dynamics : Arrow (selfMonomial state) interface -- S*Y^S -> p

functionToDynamicalSystem : (A B : Set) -> (A -> B) -> DynamicalSystem
functionToDynamicalSystem A B f = MkDynamicalSystem B (monomial B A) (id ⇄ (\_ -> f))

delay : (A : Set) -> DynamicalSystem
delay A = functionToDynamicalSystem A A id

_&&&_ : DynamicalSystem -> DynamicalSystem -> DynamicalSystem
MkDynamicalSystem stateA interfaceA dynamicsA &&& MkDynamicalSystem stateB interfaceB dynamicsB 
    = MkDynamicalSystem (stateA × stateB) (interfaceA ⊗ interfaceB) (mapPosition ⇄ mapDirection)
        where
            mapPosition : (stateA × stateB) → Polynomial.position (interfaceA ⊗ interfaceB)
            mapPosition (stateA , stateB) = (Arrow.mapPosition dynamicsA stateA) , (Arrow.mapPosition dynamicsB stateB)
            mapDirection : (state : (stateA × stateB)) -> Polynomial.direction (interfaceA ⊗ interfaceB) (mapPosition state) -> stateA × stateB
            mapDirection (sA , sB) (dirA , dirB) = (Arrow.mapDirection dynamicsA sA dirA) , (Arrow.mapDirection dynamicsB sB dirB)

Emitter : Set -> Polynomial
Emitter t = monomial t ⊤

install : (d : DynamicalSystem) -> (a : Polynomial) -> Arrow (DynamicalSystem.interface d) a -> DynamicalSystem
install d a l = MkDynamicalSystem (DynamicalSystem.state d) a (l ∘p (DynamicalSystem.dynamics d))

encloseFunction : {t u : Set} -> (t -> u) -> Arrow (monomial t u) Y
encloseFunction f = (λ _ → tt) ⇄ (λ fromPos _ → f fromPos)

auto : {m : Set} -> enclose (Emitter m)
auto = encloseFunction λ _ → tt

{-# TERMINATING #-}
run : (d : DynamicalSystem) -> enclose (DynamicalSystem.interface d) -> DynamicalSystem.state d -> Stream (Polynomial.position (DynamicalSystem.interface d)) _
run d e initialState =  [ output ] ++ (run d e next)
    where
        output : Polynomial.position (DynamicalSystem.interface d)
        output = (Arrow.mapPosition (DynamicalSystem.dynamics d) initialState)
        next : DynamicalSystem.state d
        next = Arrow.mapDirection (DynamicalSystem.dynamics d) initialState (Arrow.mapDirection e output tt)

