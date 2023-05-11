{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.SetPoly.Instance where

open import Level renaming (suc to lsuc ; zero to lzero)
open import Categories.Category
open import CategoryData.Polynomial
open import CategoryData.Lens
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Function

-- Definition of SetPoly category: Polynomials based in Set in the HoTT sense
record SetPolynomial : Set₁ where
    constructor mksetpoly 
    field
        poly : Polynomial
        isPosSet : isSet (position poly)
        isDirSet : ∀ {p : position poly} → isSet (direction poly p)
PolyAsSigma : Set₁
PolyAsSigma = Σ[ position ∈ Set ] (position → Set)

polyToSigma : Polynomial → PolyAsSigma
polyToSigma (mkpoly position direction) = position , direction
    
polyFromSigma : PolyAsSigma → Polynomial
polyFromSigma (position , direction) = mkpoly position direction

poly≡polySigma : Polynomial ≡ PolyAsSigma
poly≡polySigma = isoToPath (iso polyToSigma polyFromSigma (λ _ → refl) (λ _ → refl))

SetPolyAsSigma : Set₁
SetPolyAsSigma = Σ[ poly ∈ Polynomial ] 
                Σ[ isPosSet ∈ isSet (position poly) ] 
                    (∀ {p : position poly} → isSet (direction poly p))

isSetPolyAsSigma : isSet SetPolyAsSigma
isSetPolyAsSigma = isSetΣ {!   !} {!   !} -- Hard

open SetPolynomial

isSetPoly : isSet SetPolynomial
isSetPoly a@(mksetpoly  poly₁ isPosSet₁ isDirSet₁) b@(mksetpoly  poly₂ isPosSet₂ isDirSet₂) = {!   !}

-- position (poly (y₁ i)) != position (poly (x₁ i)) of type Type
record SetLens (from to : SetPolynomial) : Set where
    constructor ⇆ˢ
    field
        lens : Lens (poly from) (poly to)

SetLensAsSigma : (p q : SetPolynomial) → Set
SetLensAsSigma p q = Σ[ mapPos ∈ (position (poly p) → position (poly q)) ]
    ((pos : position (poly p)) → direction (poly q) (mapPos pos) → direction (poly p) pos)

isSetLensAsSigma : {p q : SetPolynomial} → isSet (SetLensAsSigma p q)
isSetLensAsSigma {p} {q} = isSetΣ (isSetΠ λ x → isPosSet q) λ x → isSetΠ λ y → isSetΠ λ z → isDirSet p {y}

lensAsSigma≡lens : {p q : SetPolynomial} → SetLens p q ≡ SetLensAsSigma p q
lensAsSigma≡lens {p} {q} = isoToPath (iso f f⁻ (λ b → refl) λ a → refl)
    where
        f : SetLens p q → SetLensAsSigma p q
        f (⇆ˢ lens) = mapPosition lens , mapDirection lens

        f⁻ : SetLensAsSigma p q → SetLens p q
        f⁻ (mapPos , mapDir) = ⇆ˢ (mapPos ⇆ mapDir)

isSetLens : {p q : SetPolynomial} → isSet (SetLens p q)
isSetLens {p} {q} = subst isSet (sym lensAsSigma≡lens) (isSetLensAsSigma {p} {q})

idSetLens : ∀ {A : SetPolynomial} → SetLens A A
idSetLens = ⇆ˢ idLens

_∘ₚₛ_ : {A B C : SetPolynomial} → SetLens B C → SetLens A B → SetLens A C
(⇆ˢ lens) ∘ₚₛ (⇆ˢ lens₁) = ⇆ˢ (lens ∘ₚ lens₁)

∘-resp-≈-set : {A B C : SetPolynomial} {f h : SetLens B C} {g i : SetLens A B} → f ≡ h → g ≡ i → (f ∘ₚₛ g) ≡ (h ∘ₚₛ i)
∘-resp-≈-set  p q ii = (p ii) ∘ₚₛ (q ii)

SetPoly : Category (lsuc lzero) lzero lzero
SetPoly = record
    { Obj = SetPolynomial
    ; _⇒_ = SetLens
    ; _≈_ = _≡_
    ; id = idSetLens
    ; _∘_ = _∘ₚₛ_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = _∙_ }
    ; ∘-resp-≈ = ∘-resp-≈-set
    }

