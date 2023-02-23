{-# OPTIONS --cubical #-}

module AgdaCategories.Functor.PlugInZero where

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


fromArrowInPolyToFunction : {A B : Polynomial} -> Arrow A B -> applyPoly A ⊥ -> applyPoly B ⊥
fromArrowInPolyToFunction {(MkPolynomial pos dir)} {B} (mapPosition ⇄ mapDirection) = \x → let
  positionAirquotes = fst x
  directionAirquoteslol = snd x
  in mapPosition positionAirquotes , λ {x₁ → directionAirquoteslol (mapDirection positionAirquotes x₁)}

appliedPolyArrowsEq : {f g : Arrow A B} -> f ≡ g -> fromArrowInPolyToFunction f ≡ fromArrowInPolyToFunction g
appliedPolyArrowsEq p i = fromArrowInPolyToFunction (p i)

appliedPolyArrowsEqPwise : {f g : Arrow A B} {z : applyPoly A ⊥} → f ≡ g -> fromArrowInPolyToFunction f z ≡ fromArrowInPolyToFunction g z
appliedPolyArrowsEqPwise {z = z} p i = let
  posEq = appliedPolyArrowsEq p i
  in posEq z

appliedPolyArrowsEqPwiseEq : {A B : Polynomial}
      {f g : Arrow A B} →
      f ≡ g →
      {z : applyPoly A ⊥} →
      fromArrowInPolyToFunction f z Eq.≡ fromArrowInPolyToFunction g z
appliedPolyArrowsEqPwiseEq p {z} = ctop (appliedPolyArrowsEqPwise {z = z} p)

-- Functor sending a polynomial the zero set "plugging in 0"
plugIn0 : Functor Poly (Sets Level.zero)
plugIn0 = record
    { F₀ = λ x → applyPoly x ⊥
    ; F₁ = fromArrowInPolyToFunction
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = appliedPolyArrowsEqPwiseEq
    }
