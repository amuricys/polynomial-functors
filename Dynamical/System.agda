{-# OPTIONS --sized-types --without-K --overlapping-instances #-}

module Dynamical.System where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary
open import Agda.Builtin.Nat renaming (_+_ to _+ℕ_)
open import CategoryData.Polynomial
open import CategoryData.Lens
open import Codata.Stream
open import Codata.Thunk
open import Data.List hiding (take; _++_)
open import Data.Vec using (Vec)
import Agda.Builtin.Nat
open import Function using (id)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import CategoryData.Everything

-- Creating dynamical systems.
record DynamicalSystem : Set₁ where
    constructor mkdyn
    field
        state : Set -- S
        interface : Polynomial -- p
        dynamics : Lens (selfMonomial state) interface -- Sy^S → p

open DynamicalSystem

record InitializedDynamicalSystem : Set₁ where
    field
        dynamicalSystem : DynamicalSystem
        initialState : Lens Y (selfMonomial (state dynamicalSystem))

functionToDynamicalSystem : (A B : Set) → (A → B) → DynamicalSystem
functionToDynamicalSystem A B f = mkdyn B (monomial B A) (id ⇆ (\_ → f))

_&&&_ : DynamicalSystem → DynamicalSystem → DynamicalSystem
mkdyn stateA interfaceA dynamicsA &&& mkdyn stateB interfaceB dynamicsB 
    = mkdyn (stateA × stateB) (interfaceA ⊗ interfaceB) ⟨ dynamicsA ⊗ dynamicsB ⟩

infixr 10 _&&&_

emitter : Set → Polynomial
emitter = linear

haltingEmitter : (A B : Set) → Polynomial
haltingEmitter A B = mkpoly (A ⊎ B) halting
    where halting : {A B : Set} → (A ⊎ B) → Set
          halting (inj₁ _) = ⊥
          halting (inj₂ _) = ⊤

install : (d : DynamicalSystem) → (a : Polynomial) → Lens (DynamicalSystem.interface d) a → DynamicalSystem
install d a l = mkdyn (DynamicalSystem.state d) a (l ∘ₚ (DynamicalSystem.dynamics d))

encloseFunction : {t u : Set} → (t → u) → Lens (monomial t u) Y
encloseFunction f = (λ _ → tt) ⇆ (λ fromPos _ → f fromPos)

auto : {m : Set} → enclose (emitter m)
auto = encloseFunction λ _ → tt

constI : {m : Set} → (i : m) → enclose (selfMonomial m)
constI i = encloseFunction λ _ → i



open import Data.Nat using (ℕ; zero; suc)

record Dimension (A : Set) : Set where
  constructor Dim
  field
    dim : ℕ

open Dimension public

-- dimProd : ∀ {A B} {{dimA : Dimension A}} {{dimB : Dimension B}} → Dimension (A × B)
-- dimProd {A} {B} {{dimA}} {{dimB}} = Dim (dim dimA +ℕ dim dimB)

-- dimNonProd : (A : Set) → ∀ {B C} → { ¬ (A ≡ (B × C))} → Dimension A
-- dimNonProd typ = Dim (suc zero)


-- instance
--   recur : ∀ {A B} {{dimA : Dimension A}} {{dimB : Dimension B}} → Dimension (A × B)
--   recur = dimProd

-- instance
--   base : ∀ {A} → ∀ {B C : Set} → { ¬ (A ≡ (B × C))} → Dimension A
--   base {A} {B} {C} {p} = dimNonProd A {B} {C} {p}

-- -- Helper function to extract the dimension of a Set with a Dimension instance
-- dimOf : ∀ {A} {{_ : Dimension A}} → ℕ
-- dimOf {{d}} = dim d

-- proof : ∀ {B C : Set} → { ¬ (A ≡ (B × C))}

-- example1 : ℕ
-- example1 = dimOf {ℕ} {{base {ℕ} {_} {_} {refl}}}

-- example2 : ℕ
-- example2 = dimOf {ℕ × ℕ × ℕ}


{-# TERMINATING #-}
run : (d : DynamicalSystem) → enclose (DynamicalSystem.interface d) → DynamicalSystem.state d → Stream (Polynomial.position (DynamicalSystem.interface d)) _
run d e initialState =  [ output ] ++ (run d e next)
    where
        output : Polynomial.position (DynamicalSystem.interface d)
        output = (Lens.mapPosition (DynamicalSystem.dynamics d) initialState)
        next : DynamicalSystem.state d
        next = Lens.mapDirection (DynamicalSystem.dynamics d) initialState (Lens.mapDirection e output tt)