{-# OPTIONS --cubical #-}

module Categorical.Poly.Exponential where

open import Categorical.Poly.Instance
import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import CategoryData.Everything
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Categorical.Poly.Product
open import Categories.Object.Product Poly
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Function using (_∘_ ; _$_)

open Polynomial
open import Cubical.PolynomialEquals
open import Cubical.Foundations.Prelude
open Polynomial

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Foundations.HLevels

p^1≡p : {p : Polynomial} → p ^ 𝟙 ≡ p
p^1≡p {p@(mkpoly pos dir)} = poly≡' pos≡ dir≡
  where
      lemma₁ : {A : Type} → (⊤ → A) ≡ A
      lemma₁ = isoToPath (iso (λ x → x tt) (λ A tt → A) (λ b → refl) λ i → refl)

      lemma₄ : {A : Type} → (A → ⊤) ≡ ⊤
      lemma₄ = isoToPath (iso (λ x → tt) (λ x x₁ → tt) (λ b → refl) λ a → refl)
      
      lemma₃ : (⊤ ⊎ ⊥) ≡ ⊤
      lemma₃ = isoToPath (iso (λ x → tt) (λ x → inj₁ tt) (λ b → refl) λ {(inj₁ a) → refl ; (inj₂ ()) })

      lemma₂ : {A : Type} → (A → ⊤ ⊎ ⊥) ≡ ⊤
      lemma₂ {A} = (cong (λ x → (A → x)) lemma₃) ∙ lemma₄

      lemma₅ : {A : Type} → (Σ[ a ∈ A ] ⊤) ≡ A
      lemma₅ = isoToPath (iso fst (λ x → x , tt) (λ b → refl) λ a → refl)

      lemma : ((index : ⊤) → Σ pos (λ i → dir i → ⊤ ⊎ ⊥)) ≡ pos
      lemma = lemma₁ ∙ cong (λ a → Σ pos a) help ∙ lemma₅
        where
          help : (λ (pos : pos) → dir pos → ⊤ ⊎ ⊥) ≡ (λ (a : pos) → ⊤)
          help = funExt (λ x → lemma₂)

      pos≡ : position (p ^ 𝟙) ≡ position p
      pos≡ = lemma

      dir≡ : direction (p ^ 𝟙) ≡ (subst (λ x → x → Type) (sym pos≡) (direction p))-- ≡ direction p
      dir≡ = funExt λ {x → hej x}
        where
          hej : (x : position (mkpoly pos dir ^ 𝟙)) → direction (mkpoly pos dir ^ 𝟙) x ≡ subst (λ x₁ → x₁ → Type) (sym pos≡) dir x
          hej hej with hej tt in eq
          ... | fst₁ , snd₁ = {!   !}

