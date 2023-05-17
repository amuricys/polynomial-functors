{-# OPTIONS --cubical #-}
module ExamplesForThesis.Examples where

-- | File contains some example code used in the written thesis.

open import Data.Integer
open import Data.Nat
open import Data.Bool
open import Cubical.Foundations.Everything

natOrBool : (b : Bool) → if b then ℕ else Bool
natOrBool true = 0
natOrBool false = true

data Either (A B : Type) : Set where
    inj₁ : A → Either A B
    inj₂ : B → Either A B

data ⊤ : Type where
    tt : ⊤

unit : {A : Type} → A → ⊤
unit _ = tt

data ⊥ : Type where

absurd : {A : Type} → ⊥ → A
absurd ()

subst' : {A : Type} {x y : A} {B : A → Type} → (x ≡ y) → B x → B y
subst' = {!   !}

absurdUnique : {A : Type} → (f : ⊥ → A) → f ≡ absurd
absurdUnique f = funExt lemma
    where
        lemma : (x : ⊥) → f x ≡ absurd x
        lemma ()

refl' : {A : Type} → {a : A} → a ≡ a
refl' {a = a} i = a