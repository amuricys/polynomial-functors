{-# OPTIONS --without-K #-}

module CategoryData.Tensor where

open import CategoryData.Polynomial
open import CategoryData.Lens
open import CategoryData.SimplePolynomials
open import Data.Product

-- Tensor between two polynomials. Parallel product.
-- Pair of position. Each pair of position has one direction for each component.
_⊗_ : Polynomial → Polynomial → Polynomial
mkpoly posA dirA ⊗ mkpoly posB dirB = mkpoly (posA × posB) (λ {(posA , posB) → (dirA posA) × (dirB posB)})
infixl 26 _⊗_

⟨_⊗_⟩ : {p q r w : Polynomial} → Lens p r → Lens q w → Lens (p ⊗ q) (r ⊗ w)
⟨_⊗_⟩ {p} {q} {r} {w} (f ⇆ f♯) (g ⇆ g♯) = mp ⇆ md
  where mp : position (p ⊗ q) → position (r ⊗ w)
        mp (posp , posq) = f posp , g posq
        md : (fromPos : position (p ⊗ q)) → direction (r ⊗ w) (mp fromPos) → direction (p ⊗ q) fromPos
        md (posp , posq) (dirr , dirw) = f♯ posp dirr , g♯ posq dirw


tensorUnit : Polynomial
tensorUnit = Y