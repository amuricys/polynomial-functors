{-# OPTIONS --cubical #-}

module AgdaCategories.Adjunction where

import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Unit
open import Data.Empty
open import Level
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Cubical.Data.Equality using (ctop ; ptoc)
open import Cubical.Foundations.Prelude
open import Common.CategoryData
open import Function
open import AgdaCategories.CubicalPoly
open import Cubical.Proofs


------- Helpers -------
-----------------------
pwiseToExt : {A B : Set} {f g : A → B} -> ({x : A} → f x Eq.≡ g x) -> f ≡ g
pwiseToExt {A = A} {f = f} {g = g} p = let
  yaaa : {x : A} → f x ≡ g x
  yaaa = ptoc p
  in
  funExt (λ x → yaaa)

positionArrowsEqual : {f g : Arrow A B} -> f ≡ g -> Arrow.mapPosition f ≡ Arrow.mapPosition g
positionArrowsEqual p i = Arrow.mapPosition (p i)

positionArrowsEqualPwise : {f g : Arrow A B} {z : Polynomial.position A} → f ≡ g -> Arrow.mapPosition f z ≡ Arrow.mapPosition g z
positionArrowsEqualPwise {z = z} p i = let
  posEq = positionArrowsEqual p i
  in posEq z

positionArrowsEqualPwiseEq : {A B : Polynomial} {f g : Arrow A B} →
      f ≡ g →
      {x : Polynomial.position A} →
      Arrow.mapPosition f x Eq.≡ Arrow.mapPosition g x
positionArrowsEqualPwiseEq p = ctop (positionArrowsEqualPwise p)
-----------------------
-----------------------

-- Functor sending a set A to the constant polynomial Ay^0 = A
constantPolynomial : Functor (Sets Level.zero) Poly 
constantPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → ⊥
    ; F₁ = λ f → f ⇄ λ fromPos → id
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ p → arrowsEqual (funExt λ x → ptoc p) refl
    }

-- Functor sending a polynomial the zero set "plugging in 0"
plugIn0 : Functor Poly (Sets Level.zero)
plugIn0 = record
    { F₀ = λ _ -> ⊥
    ; F₁ = λ f ()
    ; identity = \{A} -> λ {}
    ; homomorphism = \{X Y Z f g} -> λ {}
    ; F-resp-≈ = λ _ {}
    }

-- The two above are adjoints
-- constantPolynomial⊢plugIn0 : Adjoint constantPolynomial plugIn0
-- constantPolynomial⊢plugIn0 = record 
--     { unit = record { η = λ X x → {!   !} ; commute = λ f → {!   !} ; sym-commute = {!   !} }
--     ; counit = record { η = λ X → MkArrow (λ ()) (λ fromPos _ → fromPos) ; commute = {!   !} ; sym-commute = {!   !} }
--     ; zig = {!   !}
--     ; zag = {!   !} }

-- -- Functor sending a polynomial to its set of positions "plugging in 1"
plugIn1 : Functor Poly (Sets Level.zero)
plugIn1 = record
    { F₀ = Polynomial.position
    ; F₁ = Arrow.mapPosition
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = positionArrowsEqualPwiseEq
    }

-- -- The two above are adjoints in the other direction
-- plugIn1⊢constantPolynomial : Adjoint plugIn1 constantPolynomial
-- plugIn1⊢constantPolynomial = record 
--     { unit = {!   !}
--     ; counit = {!   !}
--     ; zig = {!   !}
--     ; zag = {!   !} }

-- Functor sending a set A to the linear polynomial Ay^1 = Ay
linearPolynomial : Functor (Sets Level.zero) Poly
linearPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → ⊤
    ; F₁ = λ f → f ⇄ \ _ _ -> tt
    ; identity = λ i → id ⇄ (λ fromPos x → x)
    ; homomorphism = λ {x y z} {f g} i → (g ∘ f) ⇄ λ fromPos k → k
    ; F-resp-≈ = λ {A B} {f g} x i → let
      cubic : f ≡ g
      cubic = pwiseToExt x
      in
        (cubic i) ⇄ λ fromPos x₁ → x₁
    }

-- linearPolynomial⊢plugIn1 : Adjoint linearPolynomial plugIn1
-- linearPolynomial⊢plugIn1 = record 
--     { unit = {!   !}
--     ; counit = {!   !}
--     ; zig = {!   !}
--     ; zag = {!   !} }
      