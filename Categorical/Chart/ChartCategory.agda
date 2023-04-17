{-# OPTIONS --cubical #-}

module Categorical.Chart.ChartCategory where

open import Categories.Category
open import Level
open import CategoryData.Chart.Core
open import CategoryData.Everything
open import Cubical.Foundations.Prelude

chartCat : Category (ℓ-suc ℓ-zero) ℓ-zero ℓ-zero
chartCat = record
    { Obj = Polynomial
    ; _⇒_ = Chart
    ; _≈_ = _≡_
    ; id = idChart
    ; _∘_ = ∘c
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = _∙_ }
    ; ∘-resp-≈ = λ p q i → ∘c (p i) (q i)
    }
    
-- idL : {x y : SetPolynomial} (f : Chart x y) → ؛c idChart f ≡ f
-- idL f = refl

-- idR : {x y : SetPolynomial} (f : Chart x y) → ؛c f idChart ≡ f
-- idR f = refl

-- assoc : {x y z w : SetPolynomial} (f : Chart x y) (g : Chart y z) (h : Chart z w) → ؛c (؛c f g) h ≡ ؛c f (؛c g h)
-- assoc f g h = refl

-- isSetChord : {x y : SetPolynomial} → isSet (Chart x y)
-- isSetChord = {!   !}

-- cat : Category (suc zero) zero
-- cat = record
--     { ob = SetPolynomial
--     ; Hom[_,_] = Chart
--     ; id = idChart
--     ; _⋆_ = ؛c
--     ; ⋆IdL = idL
--     ; ⋆IdR = idR
--     ; ⋆Assoc = assoc
--     ; isSetHom = {!   !}
--     }
