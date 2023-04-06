{-# OPTIONS --cubical #-}

module Categorical.CompositionMonoid where

open import Common.CategoryData
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs
open import Categories.Category.Monoidal
open import Categorical.CubicalPoly
open import Categories.Functor.Bifunctor
open import Cubical.ArrowEquals

open Polynomial

leftUnit : {p : Polynomial} → 𝕐 ◂ p ≡ p
leftUnit {p} = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Type} → Σ ⊤ (λ i → ⊤ → A) ≡ A
        lemma = isoToPath (iso (λ x → snd x tt) (λ x → tt , (λ _ → x)) (λ b → refl) λ a → refl)

        pos≡ : position (𝕐 ◂ p) ≡ position p
        pos≡ = lemma

        lemmaDir : {f : ⊤ → Set} → Σ ⊤ f ≡ f tt
        lemmaDir = isoToPath (iso (λ {(tt , hmm) → hmm}) (λ x → tt , x) (λ b → refl) λ a → refl)

        dir≡ : (posA : position (𝕐 ◂ p)) → direction (𝕐 ◂ p) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ (tt , hmm) = lemmaDir ∙ cong (direction p) (sym (transportRefl (hmm tt)))

rightUnit : {p : Polynomial} → p ◂ 𝕐 ≡ p
rightUnit {p} = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Type} {B : A → Type} → Σ A (λ i → B i → ⊤) ≡ A
        lemma = isoToPath (iso fst (λ x → x , λ x₁ → tt) (λ b → refl) λ a → refl)

        pos≡ : position (p ◂ 𝕐) ≡ position p
        pos≡ = lemma

        lemmaDir : {A : Type} → Σ A (λ _ → ⊤) ≡ A
        lemmaDir = isoToPath (iso fst (λ x → x , tt) (λ b → refl) λ a → refl)

        dir≡ : (posA : position (p ◂ 𝕐)) → direction (p ◂ 𝕐) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ posA = lemmaDir ∙ cong (direction p) (sym (transportRefl (fst posA)))

bifunctor : Bifunctor Poly Poly Poly
bifunctor = record
    { F₀ = λ  { (p , q) → p ◂ q }
    ; F₁ = λ { ((mpf ⇄ mdf) , (mpg ⇄ mdg)) → (λ { (a , b) → mpf a , λ { x → mpg (b (mdf a x)) } }) ⇄ λ { (x , y) (w , z) → (mdf x w) , (mdg (y (mdf x w)) z) } }
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = {!   !} -- λ x → arrow≡ (funExt (λ x₁ → {! refl  !})) {!   !}
    }

monoidal : Monoidal Poly
monoidal = record
    { ⊗ = bifunctor
    ; unit = 𝕐
    ; unitorˡ = record { 
        from = (λ { (tt , y) → y tt }) ⇄ λ { (tt , y) z → tt , z } ; 
        to = (λ { x → tt , λ _ → x }) ⇄ λ { fromPos → snd } ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; unitorʳ = record { 
        from = fst ⇄ λ { _ x → x , tt } ; 
        to = (λ x → x , (λ _ → tt)) ⇄ λ _ → fst ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; associator = record { 
        from = (λ { ((x , z) , y) → x , (λ x → z x , (λ x₁ → y (x , x₁))) }) ⇄ λ { ((_ , hmm) , bbb) (fst₂ , (what , is)) → (fst₂ , what) , is } ; 
        to = (λ { (a , b) → (a , (λ x → fst (b x))) , λ { (idk , wat) → snd (b idk) wat } }) ⇄ λ { (x , y) ((jee , idkk) , w) → jee , idkk , w } ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; unitorˡ-commute-from = refl
    ; unitorˡ-commute-to = refl
    ; unitorʳ-commute-from = refl
    ; unitorʳ-commute-to = refl
    ; assoc-commute-from = refl
    ; assoc-commute-to = refl
    ; triangle = refl
    ; pentagon = refl
    }
