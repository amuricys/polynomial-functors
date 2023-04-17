{-# OPTIONS --without-K #-}

module CategoryData.Chart.Core where

open import CategoryData.Everything
open import Function

record Chart (p q : Polynomial) : Set where
    constructor mkChart
    field
        mapPos : position p → position q
        mapDir : (i : position p) → direction p i → direction q (mapPos i)

∘c : {p q r : Polynomial} → Chart q r → Chart p q → Chart p r
∘c (mkChart f f♭) (mkChart g g♭) = mkChart (f ∘ g)  λ i x → f♭ (g i) (g♭ i x)

idChart : {p : Polynomial} → Chart p p
idChart = mkChart id λ i → id