{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.Poly.Monoidal.CompositionProduct where

open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs
open import Categories.Category.Monoidal
open import Categorical.Poly.Instance
open import Categories.Functor.Bifunctor
open import Cubical.LensEquality
open import Cubical.Data.Sigma.Properties

open Polynomial

leftUnit : {p : Polynomial} → Y ◂ p ≡ p
leftUnit {p} = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Type} → Σ ⊤ (λ i → ⊤ → A) ≡ A
        lemma = isoToPath (iso (λ x → snd x tt) (λ x → tt , (λ _ → x)) (λ b → refl) λ a → refl)

        pos≡ : position (Y ◂ p) ≡ position p
        pos≡ = lemma

        lemmaDir : {f : ⊤ → Set} → Σ ⊤ f ≡ f tt
        lemmaDir = isoToPath (iso (λ {(tt , hmm) → hmm}) (λ x → tt , x) (λ b → refl) λ a → refl)

        dir≡ : (posA : position (Y ◂ p)) → direction (Y ◂ p) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ (tt , hmm) = lemmaDir ∙ cong (direction p) (sym (transportRefl (hmm tt)))

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

open import CategoryData.Composition
assoc : {p q r : Polynomial} → (p ◂ q) ◂ r ≡ p ◂ (q ◂ r)
assoc {p} {q} {r} = poly≡∀ pos≡ dir≡
    where pos≡norm : Σ (Σ (position p) (λ i → direction p i → position q))
                       (λ i →
                           Σ (direction p (fst i)) (λ a → direction q (snd i a)) → position r)
                    ≡
                    Σ (position p)
                      (λ i →
                          direction p i →
                          Σ (position q) (λ i₃ → direction q i₃ → position r))
          pos≡norm = isoToPath (iso go back (λ _ → refl) λ _ → refl)
            where go :  Σ (Σ (position p) (λ i → direction p i → position q))
                          (λ i → Σ (direction p (fst i)) (λ a → direction q (snd i a))
                                 → position r)
                        →
                        Σ (position p)
                          (λ i →
                              direction p i →
                              Σ (position q) (λ i₃ → direction q i₃ → position r))
                  go ((posp , dirptoposq) , fromdirandfunctoposr) = 
                    posp , (λ dirp → (dirptoposq dirp) , (λ dirqatthatpos → fromdirandfunctoposr (dirp , dirqatthatpos)))
                  back : Σ (position p)
                          (λ i →
                              direction p i →
                              Σ (position q) (λ i₃ → direction q i₃ → position r)) 
                        → 
                        Σ (Σ (position p) (λ i → direction p i → position q))
                          (λ i → Σ (direction p (fst i)) (λ a → direction q (snd i a))
                                 → position r)
                  back (posp , postodir) = 
                    (posp , (λ dirp → fst (postodir dirp))) , λ { (dirp , dirq) → snd (postodir dirp) dirq }
                        
          pos≡ : position (p ◂ q ◂ r) ≡ position (p ◂ (q ◂ r))
          pos≡ = pos≡norm
          dir≡ : (posB : Σ (position p) (λ i → direction p i → position (q ◂ r))) →
                    subst (λ x → x → Type) pos≡ (dir (p ◂ q) r) posB 
                  ≡
                 dir p (q ◂ r) posB
          dir≡ (a , b) = {!   !}
bifunctor : Bifunctor Poly Poly Poly
bifunctor = record
    { F₀ = λ  { (p , q) → p ◂ q }
    ; F₁ = λ { ((mpf ⇆ mdf) , (mpg ⇆ mdg)) → (λ { (a , b) → mpf a , λ { x → mpg (b (mdf a x)) } }) ⇆ λ { (x , y) (w , z) → (mdf x w) , (mdg (y (mdf x w)) z) } }
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ x → lens≡ {!   !} {!   !}
    }

monoidal : Monoidal Poly
monoidal = record
    { ⊗ = bifunctor
    ; unit = Y
    ; unitorˡ = record { 
        from = (λ { (tt , y) → y tt }) ⇆ λ { (tt , y) z → tt , z } ; 
        to = (λ { x → tt , λ _ → x }) ⇆ λ { fromPos → snd } ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; unitorʳ = record { 
        from = fst ⇆ λ { _ x → x , tt } ; 
        to = (λ x → x , (λ _ → tt)) ⇆ λ _ → fst ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; associator = record { 
        from = (λ { ((x , z) , y) → x , (λ x → z x , (λ x₁ → y (x , x₁))) }) ⇆ λ { ((_ , hmm) , bbb) (fst₂ , (what , is)) → (fst₂ , what) , is } ; 
        to = (λ { (a , b) → (a , (λ x → fst (b x))) , λ { (idk , wat) → snd (b idk) wat } }) ⇆ λ { (x , y) ((jee , idkk) , w) → jee , idkk , w } ; 
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
 