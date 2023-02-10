open import common.Poly
open import Function
open import Categories.Category
open import Categories.Category.Instance.Sets
open import Categories.Functor
open import Level

module book.chap2 where

representable : {o : Level} -> (C : Category o o o) -> (Category.Obj C) -> Functor C (Sets o)
representable c obj = record
  { F₀ = \x -> Category.hom-setoid {?} {?} -- {obj} {x} -- \ C -> C -> Set
  ; F₁ = ?
  ; identity = {!   !}
  ; homomorphism = {!   !}
  ; F-resp-≈ = {!   !}
  }

