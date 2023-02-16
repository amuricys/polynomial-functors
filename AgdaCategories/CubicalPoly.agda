{-# OPTIONS --cubical #-}

module AgdaCategories.CubicalPoly where

open import Agda.Builtin.Nat hiding (_+_ ; _*_ )
import Agda.Builtin.Nat
open import Level
open import Categories.Category
import Categories.Object.Initial
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
import Cubical.Foundations.Prelude as Cubical
open import Cubical.Data.Sigma.Properties
open import Common.CategoryData
open import Cubical.Proofs
open import Cubical.Foundations.Prelude

-- Definition of Poly category: integration point between agda-categories and cubical
Poly  : ∀ {l1 l2 l3 : Level} -> Category (Level.suc Level.zero) Level.zero Level.zero
Poly  = record
    { Obj = Polynomial
    ; _⇒_ = Arrow
    ; _≈_ = _≡_
    ; id = idArrow
    ; _∘_ = _∘p_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = transitivity }
    ; ∘-resp-≈ = equiv-resp
    }
