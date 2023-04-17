{-# OPTIONS --cubical #-}

module Cubical.Chart.ChartArrowCommute where

open import CategoryData.Everything
open import CategoryData.Chart.Core
open import Cubical.Foundations.Prelude

ArrowChartCommute : {p₁ p₂ p₃ p₄ : Polynomial} (w : Arrow p₁ p₃) (v : Arrow p₂ p₄) (f : Chart p₁ p₂) (g : Chart p₃ p₄) → Type
ArrowChartCommute {p₁} {p₂} {p₃} {p₄} (w ⇄ w♯) (v ⇄ v♯) (mkChart f f♭) (mkChart g g♭) = Σ mapPos≡ mapDir≡
    where
        mapPos≡ : Type
        mapPos≡ = (i : position p₁) → v (f i) ≡ g (w i)

        mapDir≡ : mapPos≡ → Type
        mapDir≡ p≡ = (i : position p₁) → (x : direction p₃ (w i)) → f♭ i (w♯ i x) ≡ v♯ (f i) (subst (direction p₄) (sym (p≡ i)) (g♭ (w i) x))
