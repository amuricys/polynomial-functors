{-# OPTIONS --cubical --sized-types #-}

module Cubical.CartesianVertical where

open import Data.Bool
open import Data.Product
open import Data.Sum
open import CategoryData.Everything
open import Cubical.Core.Everything hiding (Σ-syntax)
open import Cubical.Foundations.Prelude hiding (Σ-syntax)
open import Cubical.Foundations.Isomorphism
open import Level
open import Cubical.PolynomialEquals
open import Cubical.LensEquality
open import Cubical.Data.Sigma.Properties
open import Data.Unit
open import Dynamical.System
open import Function
open import Cubical.Foundations.Path using ( toPathP⁻ )

isVertical : {p q : Polynomial} → Lens p q → Type 
isVertical (f ⇆ f♯) = isIso f

isCartesian : {p q : Polynomial} → Lens p q → Type 
isCartesian {p} (f ⇆ f♯) = (i : position p) → isIso (f♯ i)

isVerticalCompose : {p q r : Polynomial} → {g : Lens q r} → {f : Lens p q}
    → isVertical g → isVertical f → isVertical (g ∘ₚ f)
isVerticalCompose {g = g} {f = f} (g⁻ , a , b) (f⁻ , c , d)
    = f⁻ ∘ g⁻ , (λ x → cong (mapPosition g) (c (g⁻ x)) ∙ a x) , λ y → cong f⁻ (b (mapPosition f y)) ∙ d y

isCartesianCompose : {p q r : Polynomial} → {g : Lens q r} → {f : Lens p q}
    → isCartesian g → isCartesian f → isCartesian (g ∘ₚ f)
isCartesianCompose {p} {q} {r} {g} {f} pp bb h = let (a , b , c) = bb h ; (d , e , ff) = pp (mapPosition f h)
    in (d ∘ a) , (λ x → cong (mapDirection f h) (e (a x)) ∙ b x) , λ y → cong (proj₁ (pp (mapPosition f h))) (c (mapDirection g (mapPosition f h) y)) ∙ ff y

isIsoLens : {p q : Polynomial} (f : Lens p q) → Type
isIsoLens {p} {q} f = Σ[ g ∈ Lens q p ] ((g ∘ₚ f ≡ idLens) × f ∘ₚ g ≡ idLens)

addIsCartesian : {p q r t : Polynomial} {f : Lens p q} {g : Lens r t}
    → isVertical f → isVertical g → isVertical (⟨ f ⊎ g ⟩)
addIsCartesian ( a , b , c) (d , e , f) = (Data.Sum.map a d) , (λ {(inj₁ x) → cong inj₁ (b x) 
                                                                 ; (inj₂ y) → cong inj₂ (e y)}) , λ {(inj₁ x) → cong inj₁ (c x)
                                                                                                   ; (inj₂ y) → cong inj₂ (f y)}

prodIsCartesian : {p q r t : Polynomial} {f : Lens p q} {g : Lens r t}
    → isVertical f → isVertical g → isVertical (⟨ f × g ⟩)
prodIsCartesian ( a , b , c) (d , e , f) = (Data.Product.map a d) , (λ {(fst₁ , snd₁) → ΣPathP ((b fst₁) , e snd₁)}) , λ a → ΣPathP ((c (proj₁ a)) , f (snd a))

-- Identical to prodIsCartesian since behaviour of product on position is same as tensor.
tensorIsCartesian : {p q r t : Polynomial} {f : Lens p q} {g : Lens r t}
    → isVertical f → isVertical g → isVertical (⟨ f ⊗ g ⟩)
tensorIsCartesian ( a , b , c) (d , e , f) = (Data.Product.map a d) , (λ {(fst₁ , snd₁) →  ΣPathP ((b fst₁) , e snd₁)}) , λ a → ΣPathP ((c (proj₁ a)) , f (snd a)) 


-- isoIsVerticalAndCartesian : {p q : Polynomial} {f : Lens p q} → isIsoLens f ≡ (isVertical f × isCartesian f) -- {!   !}
-- isoIsVerticalAndCartesian {p} {q} {f} = isoToPath (iso (λ x → {!   !}) {!   !} {!   !} {!   !})
--     where
--         back : (isVertical f × isCartesian f) → isIsoLens f
--         back (fst₁ , snd₁) = ((fst (fst₁)) ⇆ λ fromPos x → {! fst (snd₁ (fst fst₁ fromPos)) x !}) , {!   !} 