{-# OPTIONS --cubical #-}

module AgdaCategories.ParallelProductMonoid where

open import Common.CategoryData
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs

open Polynomial

leftUnit : (p q : Polynomial) → Y ⊗ p ≡ p
leftUnit p q = poly≡2 posEq dirEq
    where
        module p = Polynomial p
        module q = Polynomial q

        lemma : {A : Set} → (Σ[ tt ∈ ⊤ ] A) ≡ A
        lemma = isoToPath (iso snd (λ x → tt , x) (λ b → refl) λ a → refl)

        posEq : position (Y ⊗ p) ≡ position p
        posEq = lemma

        dirEq : (pos : position (Y ⊗ p)) → direction (Y ⊗ p) pos ≡ direction p (subst (λ x → x) posEq pos)
        dirEq (tt , posP) = lemma ∙ cong p.direction (sym (transportRefl posP))


rightUnit : (p q : Polynomial) → p ⊗ Y ≡ p
rightUnit p q = poly≡2 posEq dirEq
    where
        lemma : {A : Set} → Σ A (λ _ → ⊤) ≡ A
        lemma = isoToPath (iso fst (λ x → x , tt) (λ b → refl) λ a → refl)

        posEq : position (p ⊗ Y) ≡ position p
        posEq = lemma

        dirEq : (pos : position (p ⊗ Y)) → direction (p ⊗ Y) pos ≡ direction p (subst (λ x → x) posEq pos)
        dirEq (fst₁ , tt) = lemma ∙ cong (direction p) (sym (transportRefl fst₁))

-- parallelProductMonoidal : Monoidal Poly
-- parallelProductMonoidal = record
--     { ⊗ = bifunctor⊗
--     -- record
--     --     { F₀ = λ { (fst , snd) → fst ⊗ snd}
--     --     ; F₁ = λ { (fst , snd) → (λ {(posX , posY) → Arrow.mapPosition fst posX , Arrow.mapPosition snd posY}) ⇄ λ {(fst₂ , snd₂) (fst₁ , snd₁) → Arrow.mapDirection fst fst₂ fst₁  , Arrow.mapDirection snd snd₂ snd₁}}
--     --     ; identity = refl
--     --     ; homomorphism = arrowsEqual3 refl λ {(fst₁ , snd₁) → λ { (fst₁ , snd₁) → {! substRefl !} }}
--     --     ; F-resp-≈ = {!   !}
--     --     }
--         ; unit = {!   !}
--     ; unitorˡ = {!   !}
--     ; unitorʳ = {!   !}
--     ; associator = {!   !}
--     ; unitorˡ-commute-from = {!   !}
--     ; unitorˡ-commute-to = {!   !}
--     ; unitorʳ-commute-from = {!   !}
--     ; unitorʳ-commute-to = {!   !}
--     ; assoc-commute-from = {!   !}
--     ; assoc-commute-to = {!   !}
--     ; triangle = {!   !}
--     ; pentagon = {!   !}
--     }
--     where
--         bifunctor⊗ : {!   !}
--         bifunctor⊗ = {!   !}