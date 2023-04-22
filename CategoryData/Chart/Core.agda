{-# OPTIONS --without-K #-}

module CategoryData.Chart.Core where

open import CategoryData.Everything
open import Function

record Chart (p q : Polynomial) : Set where
    constructor _⇉_ 
    field
        mapPos : position p → position q
        mapDir : (i : position p) → direction p i → direction q (mapPos i)

∘c : {p q r : Polynomial} → Chart q r → Chart p q → Chart p r
∘c (f ⇉ f♭) (g ⇉ g♭) = (f ∘ g) ⇉ λ i x → f♭ (g i) (g♭ i x)

idChart : {p : Polynomial} → Chart p p
idChart = id ⇉ λ _ → id