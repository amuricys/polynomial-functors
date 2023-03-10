{-# OPTIONS --cubical #-}

module AgdaCategories.CompositionMonoid where

open import Common.CategoryData
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs

leftUnit : (p q : Polynomial) → Y ◂ p ≡ p
leftUnit (MkPolynomial posP dirP) (MkPolynomial posQ dirQ) = poly≡2 (isoToPath p1) λ {(tt , fromT) → transitivity lemma (cong (λ a → dirP a) (sym (transportRefl (fromT tt))))}
    where
        p1 : Iso (Σ ⊤ (λ p → ⊤ → posP)) posP
        p1 = iso (λ {(fst₁ , snd₁) → snd₁ fst₁}) (λ x → tt , λ x₁ → x) (λ b → refl) λ {(tt , snd₁) → refl}

        lemma : {f : ⊤ → Set} → Σ ⊤ f ≡ f tt
        lemma = isoToPath (iso (λ {(tt , snd₁) → snd₁}) (λ x → tt , x) (λ b → refl) λ a → refl)

rightUnit : (p q : Polynomial) → p ◂ Y ≡ p
rightUnit p q = poly≡2 p1 λ {(fst₁ , snd₁) → transitivity (lemma fst₁ snd₁) (cong (λ a → Polynomial.direction p a) (sym (transportRefl fst₁)))}
    where
        p1 : Σ (Polynomial.position p) (λ i → Polynomial.direction p i → ⊤) ≡ Polynomial.position p
        p1 = isoToPath (iso (λ {(fst₁ , snd₁) → fst₁}) (λ x → x , λ x₁ → tt) (λ b → refl) λ a → refl)

        lemma : (fst₁ : Polynomial.position p) → (snd₁ : Polynomial.direction p fst₁ → ⊤) → Σ (Polynomial.direction p fst₁) (λ a → ⊤) ≡ Polynomial.direction p fst₁ -- (transp (λ i → Polynomial.position p) i0 fst₁)
        lemma fst snd = isoToPath (iso (λ {(fst₁ , snd₁) → fst₁}) (λ x → x , tt) (λ b → refl) λ a → refl)