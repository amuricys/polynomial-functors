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

-- Definition of Poly category: integration point between agda-categories and cubical
Poly  : ∀ {l1 l2 l3 : Level} -> Category (Level.suc Level.zero) Level.zero Level.zero
Poly  = record
    { Obj = Polynomial
    ; _⇒_ = Arrow
    ; _≈_ = Cubical._≡_
    ; id = idArrow
    ; _∘_ = _*_
    ; assoc = Cubical.refl
    ; sym-assoc = Cubical.refl
    ; identityˡ = Cubical.refl
    ; identityʳ = Cubical.refl
    ; identity² = Cubical.refl
    ; equiv = record { refl = Cubical.refl ; sym = Cubical.sym ; trans = transitivity }
    ; ∘-resp-≈ = equiv-resp
    }
