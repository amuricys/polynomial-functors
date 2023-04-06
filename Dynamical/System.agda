{-# OPTIONS --sized-types --without-K --overlapping-instances #-}

module Dynamical.System where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
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
open import Data.Empty

-- Creating dynamical systems.
record DynamicalSystem : Set₁ where
    constructor MkDynamicalSystem
    field
        state : Set -- S
        interface : Polynomial -- p
        dynamics : Arrow (selfMonomial state) interface -- Sy^S → p

open DynamicalSystem

record InitializedDynamicalSystem : Set₁ where
    field
        dynamicalSystem : DynamicalSystem
        initialState : Arrow 𝕐 (selfMonomial (state dynamicalSystem))

functionToDynamicalSystem : (A B : Set) → (A → B) → DynamicalSystem
functionToDynamicalSystem A B f = MkDynamicalSystem B (monomial B A) (id ⇄ (\_ → f))

delay : (A : Set) → DynamicalSystem
delay A = functionToDynamicalSystem A A id

_&&&_ : DynamicalSystem → DynamicalSystem → DynamicalSystem
MkDynamicalSystem stateA interfaceA dynamicsA &&& MkDynamicalSystem stateB interfaceB dynamicsB 
    = MkDynamicalSystem (stateA × stateB) (interfaceA ⊗ interfaceB) (readout ⇄ update)
        where
            readout : (stateA × stateB) → Polynomial.position (interfaceA ⊗ interfaceB)
            readout (stateA , stateB) = (Arrow.mapPosition dynamicsA stateA) , (Arrow.mapPosition dynamicsB stateB)
            update : (state : (stateA × stateB)) → Polynomial.direction (interfaceA ⊗ interfaceB) (readout state) → stateA × stateB
            update (sA , sB) (dirA , dirB) = (Arrow.mapDirection dynamicsA sA dirA) , (Arrow.mapDirection dynamicsB sB dirB)
infixr 10 _&&&_

Emitter : Set → Polynomial
Emitter t = monomial t ⊤

install : (d : DynamicalSystem) → (a : Polynomial) → Arrow (DynamicalSystem.interface d) a → DynamicalSystem
install d a l = MkDynamicalSystem (DynamicalSystem.state d) a (l ∘ₚ (DynamicalSystem.dynamics d))

encloseFunction : {t u : Set} → (t → u) → Arrow (monomial t u) 𝕐
encloseFunction f = (λ _ → tt) ⇄ (λ fromPos _ → f fromPos)

auto : {m : Set} → enclose (Emitter m)
auto = encloseFunction λ _ → tt

constI : {m : Set} → (i : m) → enclose (selfMonomial m)
constI i = encloseFunction λ _ → i

-- open import Data.Nat using (ℕ; zero; suc)

-- record Dimension (A : Set) : Set where
--   constructor Dim
--   field
--     dim : ℕ

-- open Dimension public

-- dimProd : ∀ {A B} {{dimA : Dimension A}} {{dimB : Dimension B}} → Dimension (A × B)
-- dimProd {A} {B} {{dimA}} {{dimB}} = Dim (suc (dim dimA +ℕ dim dimB))

-- dimNonProd : (A : Set) → ∀ {B C} → { ¬ (A ≡ (B × C))} → Dimension A
-- dimNonProd typ = Dim (suc zero)


-- instance
--   recur : ∀ {A B} {{dimA : Dimension A}} {{dimB : Dimension B}} → Dimension (A × B)
--   recur = dimProd

-- instance
--   base : ∀ {A} → ∀ {B C} → { ¬ (A ≡ (B × C))} → Dimension A
--   base {A} {B} {C} {p} = dimNonProd A {B} {C} {p}

-- -- Helper function to extract the dimension of a Set with a Dimension instance
-- dimOf : ∀ {A} {{_ : Dimension A}} → ℕ
-- dimOf {{d}} = dim d

-- example1 : ℕ
-- example1 = dimOf {ℕ} {{base {ℕ}}}

-- example2 : ℕ
-- example2 = dimOf {ℕ × ℕ × ℕ}


{-# TERMINATING #-}
run : (d : DynamicalSystem) → enclose (DynamicalSystem.interface d) → DynamicalSystem.state d → Stream (Polynomial.position (DynamicalSystem.interface d)) _
run d e initialState =  [ output ] ++ (run d e next)
    where
        output : Polynomial.position (DynamicalSystem.interface d)
        output = (Arrow.mapPosition (DynamicalSystem.dynamics d) initialState)
        next : DynamicalSystem.state d
        next = Arrow.mapDirection (DynamicalSystem.dynamics d) initialState (Arrow.mapDirection e output tt)

