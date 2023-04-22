{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.Instance.SetPoly where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Categories.Category
open import CategoryData.Core
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

-- Definition of SetPoly category: Polynomials based in Set in the HoTT sense

-- record Polynomial : Set₁ where
--     constructor MkPoly
--     field
--         position : Set
--         direction : position → Set
-- open Polynomial public


record SetPolynomial : Set₁ where
    constructor MkSetPoly
    field
        poly : Polynomial
        isPosSet : isSet (position poly)
        isDirSet : ∀ {p : position poly} → isSet (direction poly p)

PolyAsSigma : Set₁
PolyAsSigma = Σ[ poly ∈ Polynomial ] 
                Σ[ isPosSet ∈ isSet (position poly) ] 
                    (∀ {p : position poly} → isSet (direction poly p))

isSetPolyAsSigma : isSet PolyAsSigma
isSetPolyAsSigma = isSetΣ {!   !} {!   !} -- Hard

open SetPolynomial
isSetPoly : isSet SetPolynomial
isSetPoly a@(MkSetPoly poly₁ isPosSet₁ isDirSet₁) b@(MkSetPoly poly₂ isPosSet₂ isDirSet₂) a≡b₁ a≡b₂ i i₁ = {!   !}

-- position (poly (y₁ i)) != position (poly (x₁ i)) of type Type
record SetArrow (from to : SetPolynomial) : Set where
    constructor ⇆ˢ
    field
        arrow : Arrow (poly from) (poly to)

SetArrowAsSigma : (p q : SetPolynomial) → Set
SetArrowAsSigma p q = Σ[ mapPos ∈ (position (poly p) → position (poly q)) ]
    ((pos : position (poly p)) → direction (poly q) (mapPos pos) → direction (poly p) pos)

isSetArrowAsSigma : {p q : SetPolynomial} → isSet (SetArrowAsSigma p q)
isSetArrowAsSigma {p} {q} = isSetΣ (isSetΠ λ x → isPosSet q) λ x → isSetΠ λ y → isSetΠ λ z → isDirSet p {y}

arrowAsSigma≡arrow : {p q : SetPolynomial} → SetArrow p q ≡ SetArrowAsSigma p q
arrowAsSigma≡arrow {p} {q} = isoToPath (iso f f⁻ (λ b → refl) λ a → refl)
    where
        f : SetArrow p q → SetArrowAsSigma p q
        f (⇆ˢ arrow) = mapPosition arrow , mapDirection arrow

        f⁻ : SetArrowAsSigma p q → SetArrow p q
        f⁻ (mapPos , mapDir) = ⇆ˢ (mapPos ⇆ mapDir)

isSetArrow : {p q : SetPolynomial} → isSet (SetArrow p q)
isSetArrow {p} {q} = subst isSet (sym arrowAsSigma≡arrow) (isSetArrowAsSigma {p} {q})

idSetArrow : ∀ {A : SetPolynomial} → SetArrow A A
idSetArrow = ⇆ˢ idArrow

_∘ₚₛ_ : {A B C : SetPolynomial} → SetArrow B C → SetArrow A B → SetArrow A C
(⇆ˢ arrow) ∘ₚₛ (⇆ˢ arrow₁) = ⇆ˢ (arrow ∘ₚ arrow₁)

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

