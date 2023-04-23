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
open import CategoryData.Everything
open import Function
open import Function.Surjection hiding (id)
open import Categorical.Instance.Poly
open import Cubical.Proofs
open import Data.Bool


fromLensInPolyToFunction : {p q : Polynomial} → Lens p q → p ⦅ ⊥ ⦆  → q ⦅ ⊥ ⦆
fromLensInPolyToFunction {A} {B} = fromLensInPolyToFunctionBetweenAppliedPolys {A} {B} {⊥}

appliedPolyLensesEq : {p q : Polynomial} → {f g : Lens p q} → f ≡ g → fromLensInPolyToFunction f ≡ fromLensInPolyToFunction g
appliedPolyLensesEq p i = fromLensInPolyToFunction (p i)

appliedPolyLensesEqPwise :{p q : Polynomial} →  {f g : Lens p q} {z : p ⦅ ⊥ ⦆ } → f ≡ g → fromLensInPolyToFunction f z ≡ fromLensInPolyToFunction g z
appliedPolyLensesEqPwise {z = z} p i = let
  posEq = appliedPolyLensesEq p i
  in posEq z

appliedPolyLensesEqPwiseEq : {p q : Polynomial}
      {f g : Lens p q} →
      f ≡ g →
      {z : p ⦅ ⊥ ⦆ } →
      fromLensInPolyToFunction f z Eq.≡ fromLensInPolyToFunction g z
appliedPolyLensesEqPwiseEq p {z} = ctop (appliedPolyLensesEqPwise {z = z} p)

-- Functor sending a polynomial the zero set "plugging in 0"
plugIn0 : Functor Poly (Sets Level.zero)
plugIn0 = record
    { F₀ = λ x → x ⦅ ⊥ ⦆
    ; F₁ = fromLensInPolyToFunctionBetweenAppliedPolys
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = appliedPolyLensesEqPwiseEq
    }
