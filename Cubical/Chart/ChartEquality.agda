{-# OPTIONS --cubical #-}

module Cubical.Chart.ChartEquality where

open import CategoryData.Core
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties
open import CategoryData.Chart.Core
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport

ChartAsΣ : (p q : Polynomial) → Type
ChartAsΣ p q = Σ[ mapPos ∈ (position p → position q) ]
                    ((i : position p) → direction p i → direction q (mapPos i))

chartAsΣToChart : {p q : Polynomial} → ChartAsΣ p q → Chart p q
chartAsΣToChart (mapPos , mapDir) = mapPos ⇉ mapDir

chartToChartAsΣ : {p q : Polynomial} → Chart p q → ChartAsΣ p q
chartToChartAsΣ (mapPos ⇉ mapDir) = mapPos , mapDir

chartAsΣ≡Chart : {p q : Polynomial} → ChartAsΣ p q ≡ Chart p q
chartAsΣ≡Chart {p} {q} = isoToPath (iso chartAsΣToChart chartToChartAsΣ (λ b → refl) λ a → refl)

chartΣ≡ : {p q : Polynomial} {f g : ChartAsΣ p q}
    → (fstF≡fstG : fst f ≡ fst g)
    → subst (λ x → (i : position p) → direction p i → direction q (x i)) fstF≡fstG (snd f) ≡ snd g
    → f ≡ g
chartΣ≡ {f = f} {g = g} fstF≡fstG sndF≡sndG = ΣPathTransport→PathΣ f g (fstF≡fstG , sndF≡sndG)

open Chart
chart≡ : {p q : Polynomial} {f g : Chart p q}
    → (mapPos≡ : mapPos f ≡ mapPos g)
    → subst (λ x → (i : position p) → direction p i → direction q (x i)) mapPos≡ (mapDir f) ≡ mapDir g
    → f ≡ g
chart≡ {p} {q} {f} {g} mapPos≡ mapDir≡ = cong chartAsΣToChart (chartΣ≡ {p} {q} {chartToChartAsΣ f} {chartToChartAsΣ g} mapPos≡ mapDir≡) -- subst (λ x → {!   !}) chartAsΣ≡Chart (chartΣ≡ mapPos≡ mapDir≡)

chartΣ≡∀ : {p q : Polynomial} {f g : ChartAsΣ p q}
    → (fstF≡fstG : fst f ≡ fst g)
    → ((i : position p) → (x : direction p i) → subst (λ h → direction q (h i)) fstF≡fstG (snd f i x) ≡ snd g i x)
    → f ≡ g
chartΣ≡∀ {p} {q} {f} {g} fstF≡fstG snd≡ = ΣPathP (fstF≡fstG , funExt λ x → funExt λ p → toPathP (snd≡ x p))

chart≡∀ : {p q : Polynomial} {f g : Chart p q}
    → (mapPos≡ : mapPos f ≡ mapPos g)
    → ((i : position p) → (x : direction p i) → subst (λ h → direction q (h i)) mapPos≡ (mapDir f i x) ≡ mapDir g i x)
    → f ≡ g
chart≡∀ {p} {q} mapPos≡ mapDir≡ = cong chartAsΣToChart (chartΣ≡∀ {p} {q} mapPos≡ mapDir≡)
