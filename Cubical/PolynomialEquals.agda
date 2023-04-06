{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.PolynomialEquals where

open import CategoryData.Core
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties

PolyAsSigma : Set₁
PolyAsSigma = Σ[ position ∈ Set ] (position → Set)

polyToSigma : Polynomial → PolyAsSigma
polyToSigma (MkPoly position direction) = position , direction
    
polyFromSigma : PolyAsSigma → Polynomial
polyFromSigma (position , direction) = MkPoly position direction

poly≡polySigma : Polynomial ≡ PolyAsSigma
poly≡polySigma = isoToPath (iso polyToSigma polyFromSigma (λ _ → refl) (λ _ → refl))

polySigmas≡ : (a b : PolyAsSigma)
    → (fstA≡fstB : fst a ≡ fst b)
    -- fst a → Type , fst b → Type , subst fstA≡fst b into first one to get matching domains
    → (subst (λ x → x → Type) fstA≡fstB (snd a)) ≡ snd b
    → a ≡ b
polySigmas≡ a b fstA≡fstB sndA≡sndB = ΣPathTransport→PathΣ a b (fstA≡fstB , sndA≡sndB)

polySigmas≡' : (a b : PolyAsSigma)
    → (fstA≡fstB : fst a ≡ fst b)
    -- fst a → Type , fst b → Type , subst fstA≡fst b into second one to get matching domains
    → snd a ≡ (subst (λ x → x → Type) (sym fstA≡fstB) (snd b))
    → a ≡ b
polySigmas≡' a b fstA≡fstB sndA≡sndB = sym (ΣPathTransport→PathΣ b a (sym fstA≡fstB , sym sndA≡sndB))


open Polynomial

poly≡ : {a b : Polynomial}
    → (fstA≡fstB : position a ≡ position b)
    → (subst (λ x → x → Type) fstA≡fstB (direction a)) ≡ direction b
    → a ≡ b
poly≡ {a} {b} fstA≡fstB sndA≡sndB i = polyFromSigma (polySigmas≡ (polyToSigma a) (polyToSigma b) fstA≡fstB sndA≡sndB i)

poly≡' : {a b : Polynomial}
    → (fstA≡fstB : position a ≡ position b)
    → direction a ≡ subst (λ x → x → Type) (sym fstA≡fstB) (direction b) -- direction b (subst (λ x → x → Type) fstA≡fstB (direction a)) ≡ direction b
    → a ≡ b
poly≡' {a} {b} fstA≡fstB sndA≡sndB  i = polyFromSigma (polySigmas≡' (polyToSigma a) (polyToSigma b) fstA≡fstB sndA≡sndB i)

poly≡∀ : {a b : Polynomial}
    → (fstA≡fstB : position a ≡ position b)
    → ((posB : position b) → subst (λ x → x → Type) fstA≡fstB (direction a) posB ≡ direction b posB)
    → a ≡ b
poly≡∀ {a} {b} fstA≡fstB sndA≡sndB = poly≡ fstA≡fstB λ i x → sndA≡sndB x i

poly≡∀' : {a b : Polynomial}
    → (fstA≡fstB : position a ≡ position b)
    → ((posA : position a) → direction a posA ≡ subst (λ x → x → Type) (sym fstA≡fstB) (direction b) posA)
    → a ≡ b
poly≡∀' {a} {b} fstA≡fstB sndA≡sndB = poly≡' fstA≡fstB λ i x → sndA≡sndB x i
