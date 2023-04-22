{-# OPTIONS --cubical #-}

module Cubical.Chart.ChartArrowCommute where

open import CategoryData.Everything
open import CategoryData.Chart.Core
open import Cubical.Foundations.Prelude

ArrowChartCommute : {p₁ p₂ p₃ p₄ : Polynomial} (w : Arrow p₁ p₃) (v : Arrow p₂ p₄) (f : Chart p₁ p₂) (g : Chart p₃ p₄) → Type
ArrowChartCommute {p₁} {p₂} {p₃} {p₄} (w ⇆ w♯) (v ⇆ v♯) (f ⇉ f♭) (g ⇉ g♭) = Σ mapPos≡ mapDir≡
    where
        mapPos≡ : Type
        mapPos≡ = (i : position p₁) → v (f i) ≡ g (w i)

        mapDir≡ : mapPos≡ → Type
        mapDir≡ p≡ = (i : position p₁) → (x : direction p₃ (w i)) → f♭ i (w♯ i x) ≡ v♯ (f i) (subst (direction p₄) (sym (p≡ i)) (g♭ (w i) x))

-- Horizontal composition
horizontialComposition : {p₁ p₂ p₃ p₄ p₅ p₆ : Polynomial}
    (f : Chart p₁ p₂) (g : Chart p₃ p₄) (h : Chart p₂ p₅) (r : Chart p₄ p₆)
    (w : Arrow p₁ p₃) (v : Arrow p₂ p₄) (m : Arrow p₅ p₆)
    → ArrowChartCommute w v f g → ArrowChartCommute v m h r
    → ArrowChartCommute w m (h ∘c  f) (r ∘c g)
horizontialComposition {p₁} {p₂} {p₃} {p₄} {p₅} {p₆} f g h r w v m sq₁ sq₂ = mapPos≡ , mapDir≡
    where
        mapPos≡ : (i : position p₁) → mapPosition m (Chart.mapPos h (Chart.mapPos f i)) ≡ Chart.mapPos r (Chart.mapPos g (mapPosition w i))
        mapPos≡ i = sq₂≡ ∙ cong (Chart.mapPos r) sq₁≡
            where
                sq₁≡ : mapPosition v (Chart.mapPos f i) ≡ Chart.mapPos g (mapPosition w i)
                sq₁≡ = fst sq₁ i

                sq₂≡ : mapPosition m (Chart.mapPos h (Chart.mapPos f i)) ≡ Chart.mapPos r (mapPosition v (Chart.mapPos f i))
                sq₂≡ = fst sq₂ (Chart.mapPos f i)

        -- f♭ i (w♯ i x) ≡ v♯ (f i) (subst (direction p₄) (sym (p≡ i)) (g♭ (w i) x))
    --     Cubical.Chart.ChartArrowCommute.mapDir≡ (mapPosition w)
    --   (mapDirection w) (mapPosition m) (mapDirection m)
    --   (Chart.mapPos (h ∘c f)) (Chart.mapDir (h ∘c f))
    --   (Chart.mapPos (r ∘c g)) (Chart.mapDir (r ∘c g)) mapPos≡
        mapDir≡ : (i : position p₁) → (x : direction p₃ (mapPosition w i)) → let 
                f' = Chart.mapPos (h ∘c f)
                f♭ = Chart.mapDir (h ∘c f)
                w♯ = mapDirection w
                w' = mapPosition w
                v♯ = mapDirection m
                g♭ = Chart.mapDir (r ∘c g)

            in f♭ i (w♯ i x) ≡ v♯ (f' i) (subst (direction p₆) (sym (mapPos≡ i)) (g♭ (w' i) x))
        mapDir≡ i x = {!   !}
            where
                sq₁≡ : Chart.mapDir f i (mapDirection w i x) ≡ mapDirection v (Chart.mapPos f i) (subst (direction p₄) (λ i₃ → fst sq₁ i (~ i₃)) (Chart.mapDir g (mapPosition w i) x))
                sq₁≡ = snd sq₁ i x

                sq₂≡ : Chart.mapDir h (Chart.mapPos f i)
                    (mapDirection v (Chart.mapPos f i)
                    (subst (λ x₁ → direction p₄ x₁) (λ i₃ → fst sq₁ i (~ i₃))
                        (Chart.mapDir g (mapPosition w i) x)))
                    ≡
                    mapDirection m (Chart.mapPos h (Chart.mapPos f i))
                    (subst (direction p₆) (λ i₃ → fst sq₂ (Chart.mapPos f i) (~ i₃))
                    (Chart.mapDir r (mapPosition v (Chart.mapPos f i))
                        (subst (λ x₁ → direction p₄ x₁) (λ i₃ → fst sq₁ i (~ i₃))
                        (Chart.mapDir g (mapPosition w i) x))))
                sq₂≡ = snd sq₂ (Chart.mapPos f i)  (subst (λ x → direction p₄ x) (sym (fst sq₁ i)) (Chart.mapDir g (mapPosition w i) x))


-- Vertical composition
verticalComposition : {p₁ p₂ p₃ p₄ p₅ p₆ : Polynomial}
    (f : Chart p₁ p₂) (g : Chart p₃ p₄) (r : Chart p₅ p₆) (h : Arrow p₃ p₅)
    (w : Arrow p₁ p₃) (v : Arrow p₂ p₄) (m : Arrow p₄ p₆)
    → ArrowChartCommute w v f g → ArrowChartCommute h m g r
    → ArrowChartCommute (h ∘ₚ w) (m ∘ₚ v) f r
verticalComposition {p₁} {p₂} {p₃} {p₄} {p₅} {p₆} f g r h w v m sq₁ sq₂ = mapPos≡ , mapDir≡
    where
        mapPos≡ : (i : position p₁) → mapPosition m (mapPosition v (Chart.mapPos f i)) ≡ Chart.mapPos r (mapPosition h (mapPosition w i))
        mapPos≡ i = cong (mapPosition m) sq₁≡ ∙ sq₂≡
            where
                sq₁≡ : mapPosition v (Chart.mapPos f i) ≡ Chart.mapPos g (mapPosition w i)
                sq₁≡ = fst sq₁ i

                sq₂≡ : mapPosition m (Chart.mapPos g (mapPosition w i)) ≡ Chart.mapPos r (mapPosition h (mapPosition w i))
                sq₂≡ = fst sq₂ (mapPosition w i) -- 

        mapDir≡ = {!   !} -- impossible