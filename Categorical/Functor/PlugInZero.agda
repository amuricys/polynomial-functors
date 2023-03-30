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
open import Common.CategoryData
open import Function
open import Function.Surjection hiding (id)
open import Categorical.CubicalPoly
open import Cubical.Proofs
open import Data.Bool


fromArrowInPolyToFunction : {A B : Polynomial} -> Arrow A B -> apply A ⊥ -> apply B ⊥
fromArrowInPolyToFunction {A} {B} = fromArrowInPolyToFunctionBetweenAppliedPolys {A} {B} {⊥}

appliedPolyArrowsEq : {A B : Polynomial} -> {f g : Arrow A B} -> f ≡ g -> fromArrowInPolyToFunction f ≡ fromArrowInPolyToFunction g
appliedPolyArrowsEq p i = fromArrowInPolyToFunction (p i)

appliedPolyArrowsEqPwise :{A B : Polynomial} ->  {f g : Arrow A B} {z : apply A ⊥} → f ≡ g -> fromArrowInPolyToFunction f z ≡ fromArrowInPolyToFunction g z
appliedPolyArrowsEqPwise {z = z} p i = let
  posEq = appliedPolyArrowsEq p i
  in posEq z

appliedPolyArrowsEqPwiseEq : {A B : Polynomial}
      {f g : Arrow A B} →
      f ≡ g →
      {z : apply A ⊥} →
      fromArrowInPolyToFunction f z Eq.≡ fromArrowInPolyToFunction g z
appliedPolyArrowsEqPwiseEq p {z} = ctop (appliedPolyArrowsEqPwise {z = z} p)

-- Functor sending a polynomial the zero set "plugging in 0"
plugIn0 : Functor Poly (Sets Level.zero)
plugIn0 = record
    { F₀ = λ x → apply x ⊥
    ; F₁ = fromArrowInPolyToFunctionBetweenAppliedPolys
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = appliedPolyArrowsEqPwiseEq
    }
