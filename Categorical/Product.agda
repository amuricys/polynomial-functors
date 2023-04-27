{-# OPTIONS --cubical #-}

module Categorical.Product where

open import Categorical.Instance.Poly
open import Categories.Object.Product Poly
open import CategoryData.Everything
open import Agda.Builtin.Sigma
open import Data.Sum
open import Cubical.LensEquality
open import Cubical.Foundations.Prelude
open import Data.Product
open import Categories.Category.Monoidal
open import Categorical.Terminal
open import Cubical.LensEquality
import Categories.Category.Cartesian as Cartesian
open import Cubical.Foundations.Isomorphism


unique : {p q r : Polynomial} {h : Lens p (q * r)} {f : Lens p q} {g : Lens p r} →
    (π₁ ∘ₚ h) ≡ f →
    (π₂ ∘ₚ h) ≡ g → 
    ⟨ f , g ⟩ ≡ h
unique {p} {q} {r} {h = h} pᶠ pᵍ = (λ i → ⟨ sym pᶠ i , sym pᵍ i ⟩) ∙ lemma
    where
        mapDir≡ : (Lens.mapDirection ⟨ π₁ ∘ₚ h , π₂ ∘ₚ h ⟩) ≡ Lens.mapDirection h
        mapDir≡ = funExt λ posP → funExt λ {(inj₁ _) → refl
                                          ; (inj₂ _) → refl}
        open Polynomial
        lemma : ⟨ π₁ ∘ₚ h , π₂ ∘ₚ h ⟩ ≡ h
        lemma = lens≡ 
            refl 
            ((substRefl 
                {B = λ (h : position p → position (q * r)) → (x : position p) → direction (q * r) (h x) → direction p x}
                (Lens.mapDirection ⟨ π₁ ∘ₚ h , π₂ ∘ₚ h ⟩)
            ) ∙ mapDir≡)

prod : {A B : Polynomial} → Product A B
prod {A = A} {B = B} = record
    { A×B = A * B
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; project₁ = refl
    ; project₂ = refl
    ; unique = unique
    }

-- Universal product property. A function A→(B*C) is the same as two functions A→B and A→C
universalPropertyProduct : {p : Polynomial} {Index : Type} {generate : Index → Polynomial}
                             → Lens p (ΠPoly (Index , generate)) ≡ ((i : Index) → Lens p (generate i))
universalPropertyProduct {p} {Index} {generate} = isoToPath (iso go back (λ b → refl) λ a → refl)
    where
        go : Lens p (ΠPoly (Index , generate)) → (i : Index) → Lens p (generate i)
        go (f ⇆ f♯) index = (λ pos → f pos index) ⇆ λ pos dir → f♯ pos  (index , dir)

        back : ((i : Index) → Lens p (generate i)) → Lens p (ΠPoly (Index , generate))
        back generateLens = (λ pos index → mapPosition (generateLens index) pos) ⇆ λ {pos (index , dir) → mapDirection (generateLens index) pos dir}

