{-# OPTIONS --cubical #-}

module AgdaCategories.Adjunction where

open import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Nat hiding (_+_ ; _*_ )
import Agda.Builtin.Nat
open import Agda.Builtin.Unit
open import Data.Empty
open import Level
open import Categories.Category
import Categories.Object.Initial
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
import Cubical.Foundations.Prelude as Cubical
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

impfunExt2 : {A B : Set} {f g : A → B} →
           ({x : A} → f x ≡ g x) → f ≡ g
impfunExt2 = {!   !}


-- Functor sending a set A to the constant polynomial Ay^0 = A
constantPolynomial : Functor (Sets Level.zero) Poly 
constantPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → ⊥
    ; F₁ = λ f → MkArrow f λ fromPos ()
    ; identity = \{A} i ->  MkArrow id λ fromPos x -> {!   !}
    ; homomorphism = \{x y z} {f g} i -> MkArrow (g ∘ f) (λ fromPos ())
    ; F-resp-≈ = λ {A B} {f g} p i → MkArrow (Cubical.implicitFunExt {!   !} {!   !}) {!   !}
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
