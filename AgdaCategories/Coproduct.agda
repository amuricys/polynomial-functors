{-# OPTIONS --cubical #-}

module AgdaCategories.Coproduct where

open import AgdaCategories.CubicalPoly
open import Categories.Object.Coproduct Poly
open import Common.CategoryData
-- open import Agda.Builtin.Sigma
open import Data.Sum
open import Function
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
-- open import Data.Product

coprod : {A B : Polynomial} -> Coproduct A B
coprod {A = A} {B = B} = record
    { A+B = A + B
    ; i₁ = i₁
    ; i₂ = i₂
    ; [_,_] = [_,_]p
    ; inject₁ = refl
    ; inject₂ = refl
    ; unique = unique
    }
    where

        i₁ = inj₁ ⇄ λ _ → id
        i₂ = inj₂ ⇄ λ _ → id

        [_,_]p : {C : Polynomial} → Arrow A C → Arrow B C → Arrow (A + B) C
        [_,_]p = λ {(f ⇄ f♯) (g ⇄ g♯) → [ f , g ] ⇄ [ f♯ , g♯ ]}

        helper : {p : Polynomial} {h : Arrow (A + B) p} -> [ h ∘p i₁ , h ∘p i₂ ]p ≡ h
        helper {p = p} {h = h} = arrowsEqual (funExt λ {(inj₁ x) → refl
                                      ; (inj₂ x) → refl}) {!   !}
        
            -- where

                -- yo : PathP (λ i → (fromPos : Polynomial.position p) → Polynomial.direction ? (mapPosEq i fromPos) → Polynomial.direction p fromPos) (Arrow.mapDirection [ h ∘p i₁ , h ∘p i₂ ]p) (Arrow.mapDirection h)
                -- yo = ?

        unique : {F : Polynomial} {h : Arrow (A + B) F} {f₁ : Arrow A F} {f₂ : Arrow B F} 
            → (h ∘p i₁) ≡ f₁
            → (h ∘p i₂) ≡ f₂
            → [ f₁ , f₂ ]p ≡ h
        unique p₁ p₂ = transitivity (λ i → [ sym p₁ i , sym p₂ i ]p) helper


--         helper2 : {F : Polynomial} {h : Arrow F (A * B)} → (Arrow.mapDirection ⟨ π₁ ∘p h , π₂ ∘p h ⟩) ≡ Arrow.mapDirection h -- (λ posC → [ (λ z → Arrow.mapDirection h posC (inj₁ z)) , (λ z → Arrow.mapDirection h posC (inj₂ z)) ]) ≡ Arrow.mapDirection h --  {! λ posC → [ (λ z → Arrow.mapDirection h posC (inj₁ z)) , (λ z → Arrow.mapDirection h posC (inj₂ z)) ]) ≡ Arrow.mapDirection h  !} helper2 = {!   !}
--         helper2 = λ i fromPos x → {!   !}

--         helper : {p  : Polynomial} {h : Arrow p (A * B)} -> ⟨ π₁ ∘p h , π₂ ∘p h ⟩ ≡ h
--         helper {h = h} = arrowsEqual refl {! helper2  !} -- fromPos x → {! Arrow.mapDirection h fromPos x  !}

--         unique : {F : Polynomial} {h : Arrow F (A * B)} {f₁ : Arrow F A} {f₂ : Arrow F B} →
--             (π₁ ∘p h) ≡ f₁ →
--             (π₂ ∘p h) ≡ f₂ → 
--             ⟨ f₁ , f₂ ⟩ ≡ h
--         unique {F = F} {h = h} p₁ p₂ = transitivity (λ i → ⟨ sym p₁ i , sym p₂ i ⟩) (helper {p = F} {h = h})
