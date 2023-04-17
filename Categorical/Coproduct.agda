{-# OPTIONS --cubical #-}

module Categorical.Coproduct where

open import Categorical.Instance.SetPoly
open import Categorical.Initial
open import Categories.Object.Coproduct SetPoly
open import CategoryData.Everything
open import Data.Sum
open import Function
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Categories.Category.Monoidal
import Categories.Category.Cocartesian as Cocartesian
open import Cubical.ArrowEquals

isSet+ : ∀ {l : Level} {A B : Set l} → isSet A → isSet B → isSet (A ⊎ B)
isSet+ a b = {!   !}

isSetInj₁ : ∀ {l : Level} {A B : Set l} → isSet (A ⊎ B) → ∀ {a : A ⊎ B} → {!   !}
isSetInj₁ plus = {!   !} 

_+ˢ_ : SetPolynomial → SetPolynomial → SetPolynomial
MkSetPoly poly isPosSet isDirSet +ˢ MkSetPoly poly₁ isPosSet₁ isDirSet₁ = let
  sum = poly + poly₁
  in MkSetPoly sum (isSet+ isPosSet isPosSet₁) {!   !}

i₁ˢ : {p q : SetPolynomial} → SetArrow p (p +ˢ q)
i₁ˢ = ⇄ˢ (inj₁ ⇄ λ _ → id)
i₂ˢ : {p q : SetPolynomial} → SetArrow q (p +ˢ q)
i₂ˢ = ⇄ˢ (inj₂ ⇄ λ _ → id)

coprod : {A B : SetPolynomial} → Coproduct A B
coprod {Aˢ@(MkSetPoly A p1 p2)} {Bˢ@(MkSetPoly B q1 q2)} = record
    { A+B = Aˢ +ˢ Bˢ
    ; i₁ = i₁ˢ {Aˢ} {Bˢ}
    ; i₂ = i₂ˢ {Aˢ} {Bˢ}
    ; [_,_] = [_,_]p
    ; inject₁ = refl
    ; inject₂ = refl
    ; unique = unique
    }
    where
        [_,_]p : {Cˢ : SetPolynomial} → SetArrow Aˢ Cˢ → SetArrow Bˢ Cˢ → SetArrow (Aˢ +ˢ Bˢ) Cˢ
        [_,_]p = λ {(⇄ˢ (f ⇄ f♯)) (⇄ˢ (g ⇄ g♯)) → ⇄ˢ ([ f , g ] ⇄ [ f♯ , g♯ ])}

        open Arrow
        open Polynomial

        
        helper : {qˢ : SetPolynomial} {hˢ : SetArrow (Aˢ +ˢ Bˢ) qˢ} → [ hˢ ∘ₚₛ i₁ˢ {Aˢ} {Bˢ} , hˢ ∘ₚₛ i₂ˢ {Aˢ} {Bˢ} ]p ≡ hˢ
        helper {qˢ@(MkSetPoly q proof1 proof2)} {hˢ@(⇄ˢ h)} = cong ⇄ˢ $ arrow≡ (funExt (λ { (inj₁ x) → refl ; (inj₂ y) → refl })) (funExt λ x → {!   !})
            where lemma1 : (x : position A) → (y : direction q (mapPosition h (inj₁ x))) → y ≡ (transp (λ i → direction q (mapPosition h (inj₁ x))) i0 y)
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
        unique : {Fˢ : SetPolynomial} {hˢ@(⇄ˢ h) : SetArrow (Aˢ +ˢ Bˢ) Fˢ} {f₁ : SetArrow Aˢ Fˢ} {f₂ : SetArrow Bˢ Fˢ} 
            → (hˢ ∘ₚₛ i₁ˢ {Aˢ} {Bˢ}) ≡ f₁
            → (hˢ ∘ₚₛ i₂ˢ {Aˢ} {Bˢ}) ≡ f₂
            → [ f₁ , f₂ ]p ≡ hˢ
        unique p₁ p₂ = (λ i → [ sym p₁ i , sym p₂ i ]p) ∙ helper
 
