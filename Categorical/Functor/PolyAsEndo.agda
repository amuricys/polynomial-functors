{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.Functor.PolyAsEndo where

open import CategoryData.Everything

open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.NaturalTransformation renaming ( id to idN )
open import Categories.Category.Instance.Sets
open import Level
open import Cubical.Data.Equality
open import Function
open import CategoryData.Chart.Core

open import Cubical.Data.Equality using (ctop ; ptoc ) renaming (_≡c_ to _≡_)
import Relation.Binary.PropositionalEquality as Eq

F-resp : {p : Polynomial} {A B : Set} {f g : A → B} {x : p ⦅ A ⦆ } → f ≡ g → applyFn p f x ≡ applyFn p g x -- 
F-resp {x = posApp , dirApp} pr = λ i → posApp , (pr i) ∘  dirApp

conv : {A B : Set} {f g : A → B} → ({x : A} → f x ≡p g x) → f ≡ g
conv p = funExt λ x → ptoc $ p

asEndo : (p : Polynomial) → Functor (Sets zero) (Sets zero)
asEndo p = record
    { F₀ = λ x → p ⦅ x ⦆
    ; F₁ = λ f → applyFn p f
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = λ {_} {_} {f} {g} proof → ctop (F-resp {f = f} {g = g} (conv proof))
    }

asNatTransArr : {p q : Polynomial} → Arrow p q → NaturalTransformation (asEndo p) (asEndo q)
asNatTransArr (f ⇆ f♯) = record { 
    η = λ { X (posP , dirP) → f posP , dirP ∘ f♯ posP } ; 
    commute = λ f₁ → Eq.refl ; 
    sym-commute = λ f₁ → Eq.refl 
    }

asNatTransChart : {p q : Polynomial} → Chart p q → NaturalTransformation (asEndo p) (asEndo q)
asNatTransChart (f ⇉ f♭) = record { 
    η = λ { X (posP , dirP) → {!   !}} ;
    commute = {!   !} ;
    sym-commute = {!   !}
  }