{-# OPTIONS --cubical #-}

module Categorical.Chart.Coproduct where

open import Categorical.Chart.Instance
open import CategoryData.Everything hiding (i₁ ; i₂ ; ⟨_,_⟩)
open import CategoryData.Chart
open import Categories.Object.Coproduct ChartCat
open import Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.ChartEquality
open import Function

i₁ : {p q : Polynomial} → Chart p (p + q)
i₁ = inj₁ ⇉ λ _ → id

i₂ : {p q : Polynomial} → Chart q (p + q)
i₂ = inj₂ ⇉ λ _ → id

open Chart
[_,_]c : {p q r : Polynomial} → Chart p r → Chart q r → Chart (p + q) r
[ f ⇉ f♭ , g ⇉ g♭ ]c = [ f , g ] ⇉ [ f♭ , g♭ ]


unique : {p q r : Polynomial} {h : Chart (p + q) r} {f₁ : Chart p r} {f₂ : Chart q r}
    → ((h ∘c i₁) ≡ f₁)
    → ((h ∘c i₂) ≡ f₂)
    → [ f₁ , f₂ ]c ≡ h
unique {p = p2} {q} {h = h} p p' = (λ i → [ sym p i , sym p' i ]c) ∙ lemma
    where
        lemma : [ h ∘c i₁ , h ∘c i₂ ]c ≡ h
        lemma = chart≡∀ (funExt λ {(inj₁ x) → refl
                                 ; (inj₂ y) → refl}) λ {(inj₁ x₁) x → transportRefl (mapDir h (inj₁ x₁) x)
                                                      ; (inj₂ y) x → transportRefl (mapDir h (inj₂ y) x)}

coprod : {p q : Polynomial} → Coproduct p q
coprod {p} {q} = record
    { A+B = p + q
    ; i₁ = i₁
    ; i₂ = i₂
    ; [_,_] = [_,_]c
    ; inject₁ = refl
    ; inject₂ = refl
    ; unique = unique
    }
