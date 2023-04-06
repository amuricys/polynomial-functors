{-# OPTIONS --cubical #-}

module Categorical.Coproduct where

open import Categorical.CubicalPoly
open import Categorical.Initial
open import Categories.Object.Coproduct Poly
open import CategoryData.Core
-- open import Agda.Builtin.Sigma
open import Data.Sum
open import Function
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Categories.Category.Monoidal
import Categories.Category.Cocartesian as Cocartesian
open import Cubical.ArrowEquals
-- open import Data.Product

coprod : {A B : Polynomial} → Coproduct A B
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
        [_,_]p : {C : Polynomial} → Arrow A C → Arrow B C → Arrow (A + B) C
        [_,_]p = λ {(f ⇄ f♯) (g ⇄ g♯) → [ f , g ] ⇄ [ f♯ , g♯ ]}

        -- helper2 : {p : Polynomial} {h : Arrow (A + B) p} → (Arrow.mapDirection [ h ∘ₚ i₁ , h ∘ₚ i₂ ]p) ≡ Arrow.mapDirection h
        -- helper2 = {!   !}

        open Arrow
        open Polynomial

        
        helper : {q : Polynomial} {proof1 : isSet (position q)} {h : Arrow (A + B) q} → [ h ∘ₚ i₁ , h ∘ₚ i₂ ]p ≡ h
        helper {q} {proof1} {h} = arrow≡ (funExt (λ { (inj₁ x) → refl ; (inj₂ y) → refl })) (funExt λ x → {!   !})
           -- arrowsEqual2 (funExt λ {(inj₁ x) → refl
           --                                             ; (inj₂ y) → refl}) λ {(inj₁ x) y → cong (λ zz → mapDirection h (inj₁ x) zz) (lemma1 x y) -- subst (λ zz → {! mapDirection h (inj₁ x) zz   !}) (lemma1 x y) {!   !}
           --                                                                  ; (inj₂ y₁) y → cong (λ zz → mapDirection h (inj₂ y₁) zz) (sym (transportRefl y)) }
            where
                lemma1 : (x : position A) → (y : direction q (mapPosition h (inj₁ x))) → y ≡ (transp (λ i → direction q (mapPosition h (inj₁ x))) i0 y)
                lemma1 x y = sym (transportRefl y)
                lemma2 : ∀ {A : Set} → isSet (A → position q)
                lemma2 = isSetΠ (λ x → proof1)
                
                -- this is expanding h on both sides by the lhs of the equality we want to prove [ h ∘ₚ i₁ , h ∘ₚ i₂ ]p ≡ h
                -- e : Arrow.mapPosition [ ([ h ∘ₚ i₁ , h ∘ₚ i₂ ]p) ∘ₚ i₁ , ([ h ∘ₚ i₁ , h ∘ₚ i₂ ]p) ∘ₚ i₂ ]p ≡ Arrow.mapPosition [ h ∘ₚ i₁ , h ∘ₚ i₂ ]p
                -- e = (funExt (λ { (inj₁ x) → refl ; (inj₂ y) → refl }))
                -- lemma2 : e ≡ refl
                -- lemma2 i j (inj₁ x) = mapPosition h (inj₁ x)
                -- lemma2 i j (inj₂ y) = mapPosition h (inj₂ y)
                -- lemma3 : {x : Polynomial.position (A + B)} → (mapDirection [ h ∘ₚ i₁ , h ∘ₚ i₂ ]p) x ≡ mapDirection h x
                -- lemma3 = refl
                -- lemma4 : (mapDirection [ h ∘ₚ i₁ , h ∘ₚ i₂ ]p) ≡ mapDirection h
                -- lemma4 = ?



        -- mapDirection h (inj₁ x) y ≡
      -- mapDirection h (inj₁ x)
      -- (transp (λ i → direction p (mapPosition h (inj₁ x))) i0 y)
                                                                            
        -- helper {p = p} {h = h} = arrowsEqual (funExt λ {(inj₁ x) → refl
        --                                               ; (inj₂ y) → refl}) (funExt λ {(inj₁ x) i → {!    !}
        --                                                                            ; (inj₂ y) → {!   !}})
        -- helper {p = p} {h = h} = arrowsEqual2 (λ {i (inj₁ x) → Arrow.mapPosition h (inj₁ x)
        --                                         ; i (inj₂ y) → Arrow.mapPosition h (inj₂ y)}) λ {(inj₁ x) y → transp {!   !} i {!   !} -- sym  λ i → transp (λ i₃ → {! Polynomial.direction p (Arrow.mapPosition h (inj₂ y))  !}) i (Arrow.mapDirection h (inj₁ x) y)
        --                                                                                        ; (inj₂ y₁) y → sym {! subst  !}} -- {! subst   !} {! transport   !} -- (λ i → λ { (inj₁ x) → ? ; (inj₂ y) → ? }) {!   !} -- h(λ i →  λ {(inj₁ x) → ?
                                                        --  ; (inj₂ y) → ? }) {!   !} -- (funExt λ {(inj₁ x) → refl
                                                    --  ; (inj₂ y) → refl}) {!   !}
        -- helper {p = p} {h = h} = arrowsEqual (funExt λ {(inj₁ x) → refl
        --                                               ; (inj₂ y) → refl}) {!   !} -- (funExt λ {(inj₁ x) → {! refl   !}
        --                                                       -- ; (inj₂ y) → {! refl  !}}) -- ? arrowsEqual (funExt λ {(inj₁ x) → refl
        -- helper {p = p} {h = h} = arrowsEqual (λ i → λ {x → {!   !}}) {!   !} 

        unique : {F : Polynomial} {h : Arrow (A + B) F} {f₁ : Arrow A F} {f₂ : Arrow B F} 
            → (h ∘ₚ i₁) ≡ f₁
            → (h ∘ₚ i₂) ≡ f₂
            → [ f₁ , f₂ ]p ≡ h
        unique p₁ p₂ = (λ i → [ sym p₁ i , sym p₂ i ]p) ∙ helper


--         helper2 : {F : Polynomial} {h : Arrow F (A * B)} → (Arrow.mapDirection ⟨ π₁ ∘ₚ h , π₂ ∘ₚ h ⟩) ≡ Arrow.mapDirection h -- (λ posC → [ (λ z → Arrow.mapDirection h posC (inj₁ z)) , (λ z → Arrow.mapDirection h posC (inj₂ z)) ]) ≡ Arrow.mapDirection h --  {! λ posC → [ (λ z → Arrow.mapDirection h posC (inj₁ z)) , (λ z → Arrow.mapDirection h posC (inj₂ z)) ]) ≡ Arrow.mapDirection h  !} helper2 = {!   !}
--         helper2 = λ i fromPos x → {!   !}

--         helper : {p  : Polynomial} {h : Arrow p (A * B)} → ⟨ π₁ ∘ₚ h , π₂ ∘ₚ h ⟩ ≡ h
--         helper {h = h} = arrowsEqual refl {! helper2  !} -- fromPos x → {! Arrow.mapDirection h fromPos x  !}

--         unique : {F : Polynomial} {h : Arrow F (A * B)} {f₁ : Arrow F A} {f₂ : Arrow F B} →
--             (π₁ ∘ₚ h) ≡ f₁ →
--             (π₂ ∘ₚ h) ≡ f₂ → 
--             ⟨ f₁ , f₂ ⟩ ≡ h
--         unique {F = F} {h = h} p₁ p₂ = transitivity (λ i → ⟨ sym p₁ i , sym p₂ i ⟩) (helper {p = F} {h = h})