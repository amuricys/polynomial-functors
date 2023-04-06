{-# OPTIONS --cubical #-}

module Categorical.Functor.PlugInZero where

import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Unit
open import Data.Empty
open import Level
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation renaming ( id to idN )
open import Cubical.Data.Equality using (ctop ; ptoc)
open import Cubical.Foundations.Prelude
open import CategoryData.Core
open import Function
open import Function.Surjection hiding (id)
open import Categorical.CubicalPoly
open import Cubical.Proofs
open import Data.Bool


fromArrowInPolyToFunction : {p q : Polynomial} → Arrow p q → p ⦅ ⊥ ⦆  → q ⦅ ⊥ ⦆
fromArrowInPolyToFunction {A} {B} = fromArrowInPolyToFunctionBetweenAppliedPolys {A} {B} {⊥}

appliedPolyArrowsEq : {p q : Polynomial} → {f g : Arrow p q} → f ≡ g → fromArrowInPolyToFunction f ≡ fromArrowInPolyToFunction g
appliedPolyArrowsEq p i = fromArrowInPolyToFunction (p i)

appliedPolyArrowsEqPwise :{p q : Polynomial} →  {f g : Arrow p q} {z : p ⦅ ⊥ ⦆ } → f ≡ g → fromArrowInPolyToFunction f z ≡ fromArrowInPolyToFunction g z
appliedPolyArrowsEqPwise {z = z} p i = let
  posEq = appliedPolyArrowsEq p i
  in posEq z

appliedPolyArrowsEqPwiseEq : {p q : Polynomial}
      {f g : Arrow p q} →
      f ≡ g →
      {z : p ⦅ ⊥ ⦆ } →
      fromArrowInPolyToFunction f z Eq.≡ fromArrowInPolyToFunction g z
appliedPolyArrowsEqPwiseEq p {z} = ctop (appliedPolyArrowsEqPwise {z = z} p)

-- Functor sending a polynomial the zero set "plugging in 0"
plugIn0 : Functor Poly (Sets Level.zero)
plugIn0 = record
    { F₀ = λ x → x ⦅ ⊥ ⦆
    ; F₁ = fromArrowInPolyToFunctionBetweenAppliedPolys
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = appliedPolyArrowsEqPwiseEq
    }
