{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.PolynomialEquals where

open import Common.CategoryData
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties

ArrowAsSigma : Polynomial -> Polynomial -> Type
ArrowAsSigma A B = Σ[ mapPosition ∈ (Polynomial.position A -> Polynomial.position B) ] 
    ((fromPos : Polynomial.position A) -> Polynomial.direction B (mapPosition fromPos) -> Polynomial.direction A fromPos)

PolyAsSigma : Set₁
PolyAsSigma = Σ[ position ∈ Set ] (position → Set)

polyToSigma : Polynomial → PolyAsSigma
polyToSigma p = p.position , p.direction
    where
        module p = Polynomial p
    
polyFromSigma : PolyAsSigma → Polynomial
polyFromSigma (position , direction) = MkPolynomial position direction

polySigmaSame : Polynomial ≡ PolyAsSigma
polySigmaSame = isoToPath polySigmaIso
    where
        polySigmaIso : Iso Polynomial PolyAsSigma
        polySigmaIso = iso polyToSigma polyFromSigma (λ sigma → refl) (λ poly → refl)

polySigmas≡ : {a b : PolyAsSigma} → (fstA≡fstB : fst a ≡ fst b) → transport (λ i → fstA≡fstB i → Type) (snd a) ≡ snd b → a ≡ b
polySigmas≡ {a} {b} fstA≡fstB sndA≡sndB = ΣPathTransport→PathΣ a b (fstA≡fstB , sndA≡sndB)

open Polynomial
poly≡ : {a b : Polynomial}
    → (fstA≡fstB : position a ≡ position b)
    → (subst (λ x → x → Type) fstA≡fstB (direction a)) ≡ direction b
    → a ≡ b
poly≡ {a} {b} fstA≡fstB sndA≡sndB i = polyFromSigma (polySigmas≡ {polyToSigma a} {polyToSigma b} fstA≡fstB sndA≡sndB i)

poly≡2 : {a b : Polynomial}
    → (fstA≡fstB : position a ≡ position b)
    → ((pos : position a) → (direction a pos ≡ direction b (subst (λ x → x) fstA≡fstB pos)))
    → a ≡ b
poly≡2 {a} {b} fstA≡fstB sndA≡sndB = poly≡ fstA≡fstB (sym {!   !})

-- Poly2 : Set₁
-- Poly2 =  -- Σ[ position ∈ Set ] (position → Set)
