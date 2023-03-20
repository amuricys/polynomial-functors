{-# OPTIONS --cubical #-}

module Categorical.ParallelProductMonoid where

open import Common.CategoryData
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs

open Polynomial

leftUnit : (p q : Polynomial) → Y ⊗ p ≡ p
leftUnit p q = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Set} → (Σ[ _ ∈ ⊤ ] A) ≡ A
        lemma = isoToPath (iso snd (λ x → tt , x) (λ b → refl) λ a → refl)

        pos≡ : position (Y ⊗ p) ≡ position p
        pos≡ = lemma

        dir≡ : (posA : position (Y ⊗ p)) → direction (Y ⊗ p) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ posA = lemma ∙ cong (direction p) (sym (transportRefl (snd posA)))


rightUnit : (p q : Polynomial) → p ⊗ Y ≡ p
rightUnit p q = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Set} → Σ A (λ _ → ⊤) ≡ A
        lemma = isoToPath (iso fst (λ x → x , tt) (λ b → refl) λ a → refl)

        pos≡ : position (p ⊗ Y) ≡ position p
        pos≡ = lemma

        dir≡ : (posA : position (p ⊗ Y)) → direction (p ⊗ Y) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ posA = lemma ∙ cong (direction p) (sym (transportRefl (fst posA)))