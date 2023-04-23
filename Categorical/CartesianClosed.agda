{-# OPTIONS --cubical #-}

module Categorical.CartesianClosed where

open import CategoryData.Everything
open import Categorical.Instance.Poly

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
open import Cubical.LensEquality
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
import Categories.Category.CartesianClosed.Canonical Poly as Canonical
open import Function

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = mkpoly ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))
eval : {p q : Polynomial} → Lens ((q ^ p) * p) q
eval {p} {q} = mapPos ⇆ mapDir
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

curry : {p q r : Polynomial} → Lens (p * q) r → Lens p (r ^ q)
curry {p} {q} {r} (f ⇆ f♯) = mapPos ⇆ mapDir
    where
        eraseLeft : {A B : Set} → A ⊎ B → ⊤ ⊎ B
        eraseLeft f = [ (λ _ → inj₁ tt) , inj₂ ] f

        mapPos : position p → position (r ^ q)
        mapPos posP posQ = f (posP , posQ) , λ {dirR → eraseLeft  (f♯ (posP , posQ) dirR)}

        mapDir : (pos : position p) → direction (r ^ q) (mapPos pos) → direction p pos
        mapDir posP (posQ , dirR , g) with f♯ (posP , posQ) dirR
        ... | inj₁ x = x

uncurry : {p q r : Polynomial} → Lens p (q ^ r) → Lens (p * r) q
uncurry {p} {q} {r} (f ⇆ f♯) = mapPos ⇆ mapDir
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
ev : {A B : Polynomial} → Lens (B ^ A * A) B
ev {A} {B} = mpEv ⇆ mdEv

canonical : {A B : Polynomial} → Canonical.CartesianClosed
canonical {A} {B} = record
    { ⊤ = 𝟙
    ; _×_ = _*_
    ; ! = lensToOne
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; !-unique = lensToOneUnique
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
        curry-unique-simple : {p q r : Polynomial} → {f : Lens p (q ^ r)} → {g : Lens (p * r) q} → eval ∘ₚ (⟨ f × idLens ⟩) ≡ g → f ≡ curry g
        curry-unique-simple {p} {q} {r} {f = f ⇆ f♯} {g = g ⇆ g♯} proof = lensesEqual3 mapPos≡ mapDir≡
           where mapPos≡ : f ≡ mapPosition (curry (g ⇆ g♯))
                 mapPos≡ = {!   !}
                 mapDir≡ : (x : position p) (y : direction (q ^ r) (mapPosition (curry (g ⇆ g♯)) x)) → 
                   f♯ x (subst (λ mapPos → direction (q ^ r) (mapPos x)) (sym mapPos≡) y) 
                     ≡
                   mapDirection (curry (g ⇆ g♯)) x y
                 mapDir≡ x y = {!   !}
        -- ... | (s ⇆ s♯) = ? ⇆ {!   !}
            -- where mp : position p → (index : position r) → Σ (position q) (λ i₃ → direction q i₃ → ⊤ ⊎ direction r index)
            --       mp p ind with s ( p , ind )
            --       ... | a = a , {!   !}
            --       md = {!   !}
        eval-comp-simple : {C D E : Polynomial} → 
                    (f : Lens (E * D) C) → 
                    (ev ∘ₚ ⟨ curry f × idLens ⟩)
                    ≡ f
        eval-comp-simple {C} {D} {E} f = lensesEqual3 refl mapDir≡
            where
                mapDir≡ : (x : position (E * D))
                        → (y : direction C (mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩) x))
                        → mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩)
                                       x 
                                       (subst (λ mapPos → direction C (mapPos x)) (sym (λ _ → mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩))) y)
                            ≡ 
                          mapDirection f x y
                mapDir≡ (posE , posD) y = {!   !}
                -- path : {x : position (E * D)} → PathP
                --     (λ _ →
                --     direction C (mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩) x) →
                --     direction
                --     (mkpoly (position E) (λ z → direction E z) *
                --      mkpoly (position D) (λ z → direction D z))
                --     x)
                --     (mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩) x) (mapDirection f x)
                -- path = {!   !}
                -- mapDir≡ : (mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩)) ≡ mapDirection f
                -- mapDir≡ = funExt (λ x → path)
                -- helper2 : subst
                --             (λ mapPos →
                --                 (fromPos : position (E * D)) →
                --                 direction C (mapPos fromPos) → direction (E * D) fromPos)
                --             (λ _ → mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩))
                --             (mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩))
                --             ≡ mapDirection f
                -- helper2 = 
                --    (substRefl 
                --         { B = λ (h : position (E * D) → position C) → (x : position (E * D)) → direction C (h x) → direction (E * D) x}
                --         (mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩))
                --     ) ∙ mapDir≡
            

                                    

  
   