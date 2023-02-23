{-# OPTIONS --cubical #-}

module AgdaCategories.Functor.PlugInOne where

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
open import AgdaCategories.CubicalPoly
open import Cubical.Proofs
open import Data.Bool

fromArrowInPolyToFunction2 : {A B : Polynomial} -> Arrow A B -> applyPoly A ⊤ -> applyPoly B ⊤
fromArrowInPolyToFunction2 {(MkPolynomial pos dir)} {B} (mapPosition ⇄ mapDirection) = \x → let
  positionAirquotes = fst x
  directionAirquoteslol = snd x
  in mapPosition positionAirquotes , λ {x₁ → directionAirquoteslol (mapDirection positionAirquotes x₁)}

appliedPolyArrowsEq2 : {f g : Arrow A B} -> f ≡ g -> fromArrowInPolyToFunction2 f ≡ fromArrowInPolyToFunction2 g
appliedPolyArrowsEq2 p i = fromArrowInPolyToFunction2 (p i)

appliedPolyArrowsEqPwise2 : {f g : Arrow A B} {z : applyPoly A ⊤} → f ≡ g -> fromArrowInPolyToFunction2 f z ≡ fromArrowInPolyToFunction2 g z
appliedPolyArrowsEqPwise2 {z = z} p i = let
  posEq = appliedPolyArrowsEq2 p i
  in posEq z

appliedPolyArrowsEqPwiseEq2 : {A B : Polynomial}
      {f g : Arrow A B} →
      f ≡ g →
      {z : applyPoly A ⊤} →
      fromArrowInPolyToFunction2 f z Eq.≡ fromArrowInPolyToFunction2 g z
appliedPolyArrowsEqPwiseEq2 p {z} = ctop (appliedPolyArrowsEqPwise2 {z = z} p)

-- -- Functor sending a polynomial to its set of positions "plugging in 1"
plugIn1 : Functor Poly (Sets Level.zero)
plugIn1 = record
    { F₀ = λ x → applyPoly x ⊤
    ; F₁ = fromArrowInPolyToFunctionBetweenAppliedPolys
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = appliedPolyArrowsEqPwiseEq2
    }