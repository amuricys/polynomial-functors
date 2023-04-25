{-# OPTIONS --cubical #-}

module Categorical.Functor.PlugInOne where

import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Unit
open import Data.Empty
open import Level
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation renaming ( id to idN )
open import Cubical.Data.Equality using (pathToEq ; eqToPath)
open import Cubical.Foundations.Prelude
open import CategoryData.Everything
open import Function
open import Function.Surjection hiding (id)
open import Categorical.Instance.Poly
open import Cubical.Proofs
open import Data.Bool

fromLensInPolyToFunction2 : {p q : Polynomial} → Lens p q → p ⦅ ⊤ ⦆ → q ⦅ ⊤ ⦆
fromLensInPolyToFunction2 {(mkpoly pos dir)} {B} (mapPosition ⇆ mapDirection) = \x → let
  positionAirquotes = fst x
  directionAirquoteslol = snd x
  in mapPosition positionAirquotes , λ {x₁ → directionAirquoteslol (mapDirection positionAirquotes x₁)}

appliedPolyLensesEq2 : {p q : Polynomial} →  {f g : Lens p q} → f ≡ g → fromLensInPolyToFunction2 f ≡ fromLensInPolyToFunction2 g
appliedPolyLensesEq2 p i = fromLensInPolyToFunction2 (p i)

appliedPolyLensesEqPwise2 : {p q : Polynomial} → {f g : Lens p q} {z : p ⦅ ⊤ ⦆} → f ≡ g → fromLensInPolyToFunction2 f z ≡ fromLensInPolyToFunction2 g z
appliedPolyLensesEqPwise2 {z = z} p i = let
  posEq = appliedPolyLensesEq2 p i
  in posEq z

appliedPolyLensesEqPwiseEq2 : {p q : Polynomial}
      {f g : Lens p q} →
      f ≡ g →
      {z : p ⦅ ⊤ ⦆} →
      fromLensInPolyToFunction2 f z Eq.≡ fromLensInPolyToFunction2 g z
appliedPolyLensesEqPwiseEq2 p {z} = pathToEq (appliedPolyLensesEqPwise2 {z = z} p)

-- -- Functor sending a polynomial to its set of positions "plugging in 1"
plugIn1 : Functor Poly (Sets Level.zero)
plugIn1 = record
    { F₀ = λ x → x ⦅ ⊤ ⦆
    ; F₁ = fromLensInPolyToFunctionBetweenAppliedPolys
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = appliedPolyLensesEqPwiseEq2
    }