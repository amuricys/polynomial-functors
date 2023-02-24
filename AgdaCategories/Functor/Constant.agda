{-# OPTIONS --cubical #-}

module AgdaCategories.Functor.Constant where

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
open import AgdaCategories.CubicalPoly
open import Cubical.Proofs
open import Data.Bool


arrowsEq : {A B : Set} -> {f g : A -> B} -> {w z : A -> ⊥ -> ⊥} -> (f ≡ g) -> (w ≡ z) -> f ⇄ w ≡ g ⇄ z
arrowsEq p q ii = (p ii) ⇄ (q ii) 

arrowsEqDep : {A : Set} {B : A -> Set} {a : A} {f g : A -> B a} {w z : A -> ⊥ -> B a} -> f ≡ g -> w ≡ z -> f ⇄ w ≡ g ⇄ z
arrowsEqDep p q ii = (p ii) ⇄ (q ii)

fromAnythingToFalseToAnythingEqual : {A B : Set} {w z : A -> ⊥ -> B} -> w ≡ z
fromAnythingToFalseToAnythingEqual i x ()

fromAnythingToFalseToAnythingEqualDep : {A : Set} {B : A -> Set} {a : A} {w z : A -> ⊥ -> B a} -> w ≡ z
fromAnythingToFalseToAnythingEqualDep i x ()

-- Fully faithful functor sending a set A to the constant polynomial Ay^0 = A
constantPolynomial : Functor (Sets Level.zero) Poly 
constantPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → ⊥
    ; F₁ = λ f → f ⇄ λ fromPos → id
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ p → arrowsEqual (funExt λ x → ptoc p) refl
    }

full : Full constantPolynomial
full = record 
    { from = record 
        { _⟨$⟩_ = Arrow.mapPosition
        ; cong = positionArrowsEqualPwiseEq } 
    ; right-inverse-of = \_ -> arrowsEq refl fromAnythingToFalseToAnythingEqual
    }

faithful : Faithful constantPolynomial
faithful = λ f g x → ctop (positionArrowsEqualPwise x)

ffcp : FullyFaithful constantPolynomial
ffcp = full , faithful