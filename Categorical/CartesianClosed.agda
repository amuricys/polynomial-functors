{-# OPTIONS --cubical #-}

module Categorical.CartesianClosed where

open import CategoryData.Everything
open import Categorical.CubicalPoly

import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (Σ-syntax ; curry ; uncurry)
open import Categorical.Product
open import Categories.Object.Product Poly
open import Categorical.Terminal
open import Cubical.Proofs
open import Cubical.ArrowEquals
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
import Categories.Category.CartesianClosed.Canonical Poly as Canonical

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = MkPoly ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))
eval : {p q : Polynomial} → Arrow ((q ^ p) * p) q
eval {p} {q} = mapPos ⇄ mapDir
    where
        mapPos : position ((q ^ p) * p) → position q
        mapPos (posQ^P , posP) = fst (posQ^P posP)

        mapDir : (pos : position ((q ^ p) * p))
            → direction q (mapPos pos) 
            → direction ((q ^ p) * p) pos
        mapDir (posQ^P , posP) dir with (snd (posQ^P posP)) dir in eq
        ... | inj₂ y = inj₂ y
        ... | inj₁ x = inj₁ (posP , dir , help)
            where
                help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posQ^P posP) dir)
                help rewrite eq = tt

curry : {p q r : Polynomial} → Arrow (p * q) r → Arrow p (r ^ q)
curry {p} {q} {r} (f ⇄ f♯) = mapPos ⇄ mapDir
    where
        eraseLeft : {A B : Set} → A ⊎ B → ⊤ ⊎ B
        eraseLeft f = [ (λ _ → inj₁ tt) , inj₂ ] f

        mapPos : position p → position (r ^ q)
        mapPos posP posQ = f (posP , posQ) , λ {dirR → eraseLeft  (f♯ (posP , posQ) dirR)}

        mapDir : (pos : position p) → direction (r ^ q) (mapPos pos) → direction p pos
        mapDir posP (posQ , dirR , g) with f♯ (posP , posQ) dirR
        ... | inj₁ x = x

uncurry : {p q r : Polynomial} → Arrow p (q ^ r) → Arrow (p * r) q
uncurry {p} {q} {r} (f ⇄ f♯) = mapPos ⇄ mapDir
    where
        mapPos : position (p * r) → position q
        mapPos (posP , posR) = fst (f posP posR)

        mapDir : (pos : position (p * r)) → direction q (mapPos pos) → direction (p * r) pos
        mapDir (posP , posR) dirQ with snd (f posP posR) dirQ in eq
        ... | inj₂ y = inj₂ y
        ... | inj₁ x = inj₁ (f♯ posP (posR , dirQ , help))
            where
                help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (f posP posR) dirQ)
                help rewrite eq = tt

mpEv : {A B : Polynomial} → position (B ^ A * A) → position B
mpEv (posB^A , posA) = fst (posB^A posA)
mdEv : {A B : Polynomial} → (fromPos : position (B ^ A * A)) → direction B (mpEv fromPos) → direction (B ^ A * A) fromPos
mdEv (posB^A , posA) x with (snd (posB^A posA)) x in eq
... | inj₂ v = inj₂ v
... | inj₁ s = inj₁ (posA , x , help eq)
        where help : (snd (posB^A posA) x) Eq.≡ inj₁ s → [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posB^A posA) x)
              help p rewrite p = tt
ev : {A B : Polynomial} → Arrow (B ^ A * A) B
ev {A} {B} = mpEv ⇄ mdEv

canonical : {A B : Polynomial} → Canonical.CartesianClosed
canonical {A} {B} = record
    { ⊤ = 𝟙
    ; _×_ = _*_
    ; ! = arrowToOne
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; !-unique = arrowToOneUnique
    ; π₁-comp = refl
    ; π₂-comp = refl
    ; ⟨,⟩-unique = unique
    ; _^_ = _^_
    ; eval = eval
    ; curry = curry
    ; eval-comp =  {!   !}
    ; curry-resp-≈ = cong curry
    ; curry-unique = {!   !}
    }
       where
        eval-comp-simple : {C D E : Polynomial} → 
                    (f : Arrow (E * D) C) → 
                    (ev ∘ₚ ⟨ curry f × idArrow ⟩)
                    ≡ f
        eval-comp-simple {C} {D} {E} f = arrow≡ refl helper2
            where
                path : {x : position (E * D)} → PathP
                    (λ _ →
                    direction C (mapPosition (ev ∘ₚ ⟨ curry f × idArrow ⟩) x) →
                    direction
                    (MkPoly (position E) (λ z → direction E z) *
                     MkPoly (position D) (λ z → direction D z))
                    x)
                    (mapDirection (ev ∘ₚ ⟨ curry f × idArrow ⟩) x) (mapDirection f x)
                path = {!   !}
                mapDir≡ : (mapDirection (ev ∘ₚ ⟨ curry f × idArrow ⟩)) ≡ mapDirection f
                mapDir≡ = funExt (λ x → path)
                helper2 : subst
                            (λ mapPos →
                                (fromPos : position (E * D)) →
                                direction C (mapPos fromPos) → direction (E * D) fromPos)
                            (λ _ → mapPosition (ev ∘ₚ ⟨ curry f × idArrow ⟩))
                            (mapDirection (ev ∘ₚ ⟨ curry f × idArrow ⟩))
                            ≡ mapDirection f
                helper2 = 
                   (substRefl 
                        { B = λ (h : position (E * D) → position C) → (x : position (E * D)) → direction C (h x) → direction (E * D) x}
                        (mapDirection (ev ∘ₚ ⟨ curry f × idArrow ⟩))
                    ) ∙ mapDir≡
            

                                    

  
   