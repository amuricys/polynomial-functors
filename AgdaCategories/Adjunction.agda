{-# OPTIONS --cubical #-}

module AgdaCategories.Adjunction where

open import Agda.Builtin.Nat hiding (_+_ ; _*_ )
import Agda.Builtin.Nat
import Agda.Builtin.Equality as Eq
open import Agda.Builtin.Unit
open import Data.Empty
open import Level
open import Categories.Category
import Categories.Object.Initial
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma.Properties
open import Common.CategoryData
open import Cubical.Proofs
open import Function
open import AgdaCategories.CubicalPoly


-- ∀ {X Y Z} {f : X -> Y} {g : Y -> Z} →
--   D [ F₁ (C [ g ∘ f ]) ≈ D [ F₁ g ∘ F₁ f ] ]
-- constHomomorph : {X Y Z : Set} {f : X → Y} {g : Y → Z} → 
--   MkArrow (λ x → g (f x)) (λ fromPos ()) 
--   ≡ 
--   MkArrow (λ x → g (f x)) (λ fromPos z → (λ ()) ((λ ()) z))
-- constHomomorph {f = f} {g = g} i = MkArrow (g ∘ f) (λ fromPos ())



-- idProof : {A : Set} -> {f g : Arrow (Constant {A}) (Constant {A})} -> (λ x → x) -> MkArrow (λ x → x) (λ fromPos ()) ≡ MkArrow (λ x → x) (λ fromPos toDir → toDir)
-- idProof = refl

-- equiv-resp : {A B C : Polynomial} {f h : Arrow B C} {g i : Arrow A B} → f ≡ h → g ≡ i → (f ∘p g) ≡ (h ∘p i)
-- equiv-resp  p q ii = (p ii) ∘p (q ii)

eqsEq : ∀ {A : Set} -> ∀ {x y : A} -> x Eq.≡ y -> x ≡ y
eqsEq Eq.refl = refl

pwiseToExt : {A B : Set} {f g : A → B} -> ({x : A} → f x Eq.≡ g x) -> f ≡ g
pwiseToExt {A = A} {f = f} {g = g} p = let
  yaaa : {x : A} → f x ≡ g x
  yaaa = eqsEq p
  in
  funExt (λ x → yaaa)

-- pwise : {A B : Set} {f g : A -> B} -> {x : A} → f x Eq.≡ g x -> f ≡ g
-- pwise p = funExt {!   !}
--   where pcubical = eqsEq {! !}

arrowsEq : {A B : Set} -> {f g : A -> B} -> {w z : A -> ⊥ -> ⊥} -> (f ≡ g) -> (w ≡ z) -> MkArrow f w ≡ MkArrow g z
arrowsEq p q ii = MkArrow (p ii) (q ii)

fromAnythingToFalseToFalseEqual : {A : Set} {w z : A -> ⊥ -> ⊥} -> w ≡ z
fromAnythingToFalseToFalseEqual i x ()

-- Functor sending a set A to the constant polynomial Ay^0 = A
constantPolynomial : Functor (Sets Level.zero) Poly 
constantPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → ⊥
    ; F₁ = λ f → MkArrow f λ fromPos ()
    ; identity = arrowsEq refl fromAnythingToFalseToFalseEqual
    ; homomorphism = \{x y z} {f g} i -> MkArrow (g ∘ f) (λ fromPos ())
    ; F-resp-≈ = λ x → arrowsEq (pwiseToExt x) fromAnythingToFalseToFalseEqual
    }

-- -- Functor sending a polynomial the zero set "plugging in 0"
-- plugIn0 : Functor Poly  (Sets Level.zero)
-- plugIn0 = record
--     { F₀ = λ _ -> ⊥
--     ; F₁ = λ f ()
--     ; identity = {!   !}
--     ; homomorphism = {!   !}
--     ; F-resp-≈ = {!   !}
--     }

-- -- The two above are adjoints
-- polyAdjoint : Adjoint constantPolynomial plugIn0
-- polyAdjoint = record 
--     { unit = {!   !}
--     ; counit = {!   !}
--     ; zig = {!   !}
--     ; zag = {!   !} }

-- -- Functor sending a polynomial to its set of positions "plugging in 1"
-- plugIn1 : Functor Poly  (Sets Level.zero)
-- plugIn1 = record
--     { F₀ = Polynomial.position
--     ; F₁ = Arrow.mapPosition
--     ; identity = {!   !}
--     ; homomorphism = {!   !}
--     ; F-resp-≈ = {!   !}
--     }

-- -- The two above are adjoints "in the other direction"; i.e. plugIn1 is a RIGHT adjoint to constantPolynomial,
-- -- which itself is a left adjoint to plugIn0
-- polyAdjoint2 : Adjoint plugIn1 constantPolynomial
-- polyAdjoint2 = record 
--     { unit = {!   !}
--     ; counit = {!   !}
--     ; zig = {!   !}
--     ; zag = {!   !} }

-- -- Functor sending a set A to the linear polynomial Ay^1 = Ay
-- linearPolynomial : Functor (Sets Level.zero) Poly
-- linearPolynomial = record
--     { F₀ = λ x → MkPolynomial x λ _ → ⊤
--     ; F₁ = λ f → MkArrow f \ _ _ -> tt
--     ; identity = {!   !}
--     ; homomorphism = {!   !}
--     ; F-resp-≈ = {!   !}
--     }

-- polyAdjoint3 : Adjoint linearPolynomial plugIn1
-- polyAdjoint3 = record 
--     { unit = {!   !}
--     ; counit = {!   !}
--     ; zig = {!   !}
--     ; zag = {!   !} }
    