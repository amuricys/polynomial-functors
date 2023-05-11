{-# OPTIONS --without-K #-}

module CategoryData.Chart where

open import CategoryData.Polynomial
open import Function

record Chart (p q : Polynomial) : Set where
    constructor _⇉_
    field
        mapPos : position p → position q
        mapDir : (i : position p) → direction p i → direction q (mapPos i)

_∘c_ : {p q r : Polynomial} → Chart q r → Chart p q → Chart p r
(f ⇉ f♭) ∘c (g ⇉ g♭) = (f ∘ g) ⇉ λ i x → f♭ (g i) (g♭ i x)

idChart : {p : Polynomial} → Chart p p
idChart = id ⇉ λ _ → id