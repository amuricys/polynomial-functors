{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.Instance.SetPoly where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Categories.Category
open import CategoryData.Core
open import Cubical.Proofs
open import Cubical.Foundations.Prelude

-- Definition of SetPoly category: Polynomials based in Set in the HoTT sense
record SetPolynomial : Set₁ where
    constructor MkSetPoly
    field
        poly : Polynomial
        isPosSet : isSet (position poly)
        isDirSet : ∀ {p : position poly} → isSet (direction poly p)

open SetPolynomial
isSetPoly : isSet SetPolynomial
isSetPoly = λ x y x₁ y₁ → {!   !}

record SetArrow (from to : SetPolynomial) : Set where
    constructor ⇄ˢ
    field
        arrow : Arrow (poly from) (poly to)

idSetArrow : ∀ {A : SetPolynomial} → SetArrow A A
idSetArrow = ⇄ˢ idArrow

_∘ₚₛ_ : {A B C : SetPolynomial} → SetArrow B C → SetArrow A B → SetArrow A C
(⇄ˢ arrow) ∘ₚₛ (⇄ˢ arrow₁) = ⇄ˢ (arrow ∘ₚ arrow₁)

equiv-resp-set : {A B C : SetPolynomial} {f h : SetArrow B C} {g i : SetArrow A B} → f ≡ h → g ≡ i → (f ∘ₚₛ g) ≡ (h ∘ₚₛ i)
equiv-resp-set  p q ii = (p ii) ∘ₚₛ (q ii)

SetPoly : Category (lsuc lzero) lzero lzero
SetPoly = record
    { Obj = SetPolynomial
    ; _⇒_ = SetArrow
    ; _≈_ = _≡_
    ; id = idSetArrow
    ; _∘_ = _∘ₚₛ_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = transitivity }
    ; ∘-resp-≈ = equiv-resp-set
    }

