{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.Poly.Functor.PolyAsEndo where

open import CategoryData.Everything

open import Categories.Category.Core
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation renaming ( id to idN )
open import Categories.Category.Instance.Sets
open import Categories.Category.Instance.Setoids
open import Level
open import Function
open import CategoryData.Chart
-- open import Categories.Functor.Representable

open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality using (pathToEq ; eqToPath )
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary.Bundles
open import Data.Product
F-resp : {p : Polynomial} {A B : Set} {f g : A → B} {x : p ⦅ A ⦆ } → f ≡ g → applyFn p f x ≡ applyFn p g x -- 
F-resp {x = posApp , dirApp} pr = λ i → posApp , (pr i) ∘  dirApp

conv : {A B : Set} {f g : A → B} → ({x : A} → f x Eq.≡ g x) → f ≡ g
conv p = funExt λ x → eqToPath $ p

asEndo : (p : Polynomial) → Functor (Sets zero) (Sets zero)
asEndo p = record
    { F₀ = λ x → p ⦅ x ⦆
    ; F₁ = λ f → applyFn p f
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = λ {_} {_} {f} {g} proof → pathToEq (F-resp {f = f} {g = g} (conv proof))
    }


asEndoSetoid : (p : Polynomial) → Functor (Setoids zero zero) (Setoids zero zero)
asEndoSetoid p = record
    { F₀ = F₀
    ; F₁ = λ { record { _⟨$⟩_ = _⟨$⟩_ ; cong = cong } → record { _⟨$⟩_ = λ { (fst₁ , snd₁) → fst₁ , (((λ { y → {! applyFn p  !} }) ∘  _⟨$⟩_) ∘  snd₁) } ; cong = {!   !} }}
    ; identity = {!   !}
    ; homomorphism = {!   !}
    ; F-resp-≈ = {!   !} -- λ {_} {_} {f} {g} proof → pathToEq (F-resp {f = f} {g = g} (conv proof))
    }
    where F₀ : Setoid ℓ-zero ℓ-zero → Setoid ℓ-zero ℓ-zero
          F₀ record { Carrier = x ; _≈_ = _≈_ ; isEquivalence = isEq } = 
            record { Carrier = p ⦅ x ⦆ ; 
                     _≈_ = _≡_; 
                     isEquivalence = record { refl = refl ; sym = sym ; trans = _∙_ } }
 
-- A Presheaf (into Setoids) is representation if it is naturally isomorphic to a Hom functor
--  over a particular object A of the base category.
open import Level

asEndoFn : {a : Set} → (p : Polynomial) → Functor (Category.op (Sets zero)) (Sets zero)
asEndoFn {a} p = record
    { F₀ = λ x → (x → a)
    ; F₁ = λ f → _∘ f
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = λ x {xa} → pathToEq (funExt λ x₁ → cong xa (eqToPath (x {x₁}))) 
    }

open import Categories.Category using (Category)
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor)
open import Categories.Functor.Hom
open import Categories.Functor.Presheaf
open import Categories.NaturalTransformation.NaturalIsomorphism

record Representable {o ℓ e} {C : Category o ℓ e} (F : Presheaf C (Sets zero)) : Set _ where
  open Category C
  open Hom C
  field
    A : Obj
    Iso : NaturalIsomorphism F {!   !}


asNatTransArr : {p q : Polynomial} → Lens p q → NaturalTransformation (asEndo p) (asEndo q)
asNatTransArr (f ⇆ f♯) = record { 
    η = λ { X (posP , dirP) → f posP , dirP ∘ f♯ posP } ; 
    commute = λ f₁ → Eq.refl ; 
    sym-commute = λ f₁ → Eq.refl 
    }

open import CategoryData.Chart

asNatTransChart : {p q : Polynomial} → Chart p q → NaturalTransformation (asEndo p) (asEndo q)
asNatTransChart (f ⇉ f♯) = record { 
    η = λ { X (posP , dirP) → (f posP) , (λ x → dirP {!   !}) } ; 
    commute = λ f₁ → {!   !} ; 
    sym-commute = λ f₁ → {!   !} 
    }

monomialsAreRepresentables : {A B : Set} → Representable {C = (Sets zero)} {!   !}
monomialsAreRepresentables = {!   !} 