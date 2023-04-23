{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Chart.ChartEquality where

open import CategoryData.Core
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties
open import CategoryData.Chart.Core

ChartAsΣ : (p q : Polynomial) → Type
ChartAsΣ p q = Σ[ mapPos ∈ (position p → position q) ]
                    ((i : position p) → direction p i → direction q (mapPos i))

chartAsΣToChart : {p q : Polynomial} → ChartAsΣ p q → Chart p q
chartAsΣToChart (mapPos , mapDir) = mkChart mapPos mapDir

chartToChartAsΣ : {p q : Polynomial} → Chart p q → ChartAsΣ p q
chartToChartAsΣ (mkChart mapPos mapDir) = mapPos , mapDir

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
chartΣ≡∀ {p} {q} {f} {g} fstF≡fstG snd≡ = chartΣ≡ {p} {q} fstF≡fstG (funExt (λ x → funExt λ y → lemma x y ∙ snd≡ x y))
    where

        lemma3 : (x : position p) (y : direction p x) → subst (λ h → direction q (h x)) fstF≡fstG (snd f x y) ≡ subst (λ h → direction q (h x)) fstF≡fstG (snd f x y)
        lemma3 x y = refl

        lemma2 : (x : position p) (y : direction p x) → subst (λ h → direction p x → direction q (h x)) fstF≡fstG (snd f x) y ≡ subst (λ h → direction q (h x)) fstF≡fstG (snd f x y)
        lemma2 x y = cong (transp (λ i → direction q (fstF≡fstG i x)) i0) (cong (snd f x) (transportRefl y)) ∙ lemma3 x y

        lemma : (x : position p) (y : direction p x) → subst (λ h → (i : position p) → direction p i → direction q (h i)) fstF≡fstG (snd f) x y ≡ subst (λ h → direction q (h x)) fstF≡fstG (snd f x y)
        lemma x y = {!   !} ∙ lemma2 x y 


chart≡∀ : {p q : Polynomial} {f g : Chart p q}
    → (mapPos≡ : mapPos f ≡ mapPos g)
    → ((i : position p) → (x : direction p i) → subst (λ h → direction q (h i)) mapPos≡ (mapDir f i x) ≡ mapDir g i x)
    → f ≡ g
chart≡∀ {p} {q} mapPos≡ mapDir≡ = cong chartAsΣToChart (chartΣ≡∀ {p} {q} mapPos≡ mapDir≡)

-- lensSigmasEqual3 : {p q : Polynomial} {f g : Lens p q}
--     → (mapPosEq : Lens.mapPosition f ≡ Lens.mapPosition g)
--     → ((x : position p) → (y : direction q (mapPosition g x)) → mapDirection f x  (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) ≡ mapDirection g x y)
--     → lensToSigma f ≡ lensToSigma g
-- lensSigmasEqual3 {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq = ΣPathTransport→PathΣ (lensToSigma f) (lensToSigma g) (mapPosEq , funExt λ x  → funExt λ y → (lemma x y) ∙ (mapDirEq x y))
--   where
--     lemma : (x : position p) → (y : direction q (mapPosition g x)) → 
--       (subst (λ h → (i : position p) → direction q (h i) → direction p i) mapPosEq (mapDirection f)) x y
--       ≡
--       mapDirection f x
--       (subst (λ h → direction q (h x)) (sym mapPosEq) y)
--     lemma x y i = transp (λ j → direction p (transp (λ _ → position p) (j ∨ i) x)) i ((mapDirection f (transp (λ _ → position p) i x) (transp (λ j → direction q (mapPosEq (~ j) (transp (λ _ → position p) (~ j ∨ i) x))) i0 y))) 


-- lensesEqual3 : {p q : Polynomial} {f g : Lens p q}
--     → (mapPosEq : mapPosition f ≡ mapPosition g)
--     → (
--            (x : position p) → 
--            (y : direction q (mapPosition g x)) → 
--            mapDirection f x  
--            (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) 
--            ≡ 
--            mapDirection g x y
--         )
--     → f ≡ g
-- lensesEqual3 {f = f} {g = g} a b i = sigmaToLens (lensSigmasEqual3 {f = f} {g = g} a b i)
