{-# OPTIONS --cubical #-}

module Categorical.CompositionMonoid where

open import Common.CategoryData
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs

open Polynomial

leftUnit : {p : Polynomial} → Y ◂ p ≡ p
leftUnit {p} = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Type} → Σ ⊤ (λ i → ⊤ → A) ≡ A
        lemma = isoToPath (iso (λ x → snd x tt) (λ x → tt , (λ _ → x)) (λ b → refl) λ a → refl)

        pos≡ : position (Y ◂ p) ≡ position p
        pos≡ = lemma

        lemmaDir : {f : ⊤ → Set} → Σ ⊤ f ≡ f tt
        lemmaDir = isoToPath (iso (λ {(tt , snd₁) → snd₁}) (λ x → tt , x) (λ b → refl) λ a → refl)

        dir≡ : (posA : position (Y ◂ p)) → direction (Y ◂ p) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ (tt , snd₁) = lemmaDir ∙ cong (direction p) (sym (transportRefl (snd₁ tt)))

rightUnit : {p : Polynomial} → p ◂ Y ≡ p
rightUnit {p} = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Type} {B : A → Type} → Σ A (λ i → B i → ⊤) ≡ A
        lemma = isoToPath (iso fst (λ x → x , λ x₁ → tt) (λ b → refl) λ a → refl)

        pos≡ : position (p ◂ Y) ≡ position p
        pos≡ = lemma

        lemmaDir : {A : Type} → Σ A (λ _ → ⊤) ≡ A
        lemmaDir = isoToPath (iso fst (λ x → x , tt) (λ b → refl) λ a → refl)

        dir≡ : (posA : position (p ◂ Y)) → direction (p ◂ Y) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ posA = lemmaDir ∙ cong (direction p) (sym (transportRefl (fst posA)))
