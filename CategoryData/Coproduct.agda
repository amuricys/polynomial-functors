{-# OPTIONS --without-K #-}

module CategoryData.Coproduct where

open import CategoryData.Core
open import CategoryData.SimplePolynomials
open import Data.Sum
open import Data.Product using (Σ-syntax ; _,_)
open import Function

-- Coproduct has either of the positions, and its correspoding direction
_+_ : Polynomial → Polynomial → Polynomial
mkpoly posA dirA + mkpoly posB dirB = mkpoly (posA ⊎ posB) [ dirA , dirB ]
infixl 28 _+_

coproductUnit : Polynomial
coproductUnit = 𝟘

-- Canonical injections
i₁ : {p q : Polynomial} → Lens p (p + q)
i₁ = inj₁ ⇆ λ _ → id
i₂ : {p q : Polynomial} → Lens q (p + q)
i₂ = inj₂ ⇆ λ _ → id

-- The unique factorizer of two lenses
[_,_]ₚ : {p q r : Polynomial} → Lens p r → Lens q r → Lens (p + q) r
[ f ⇆ f♯ , g ⇆ g♯ ]ₚ = [ f , g ] ⇆ [ f♯ , g♯ ]

⟨_⊎_⟩ : {p q r w : Polynomial} → (f : Lens p r) (g : Lens q w) → Lens (p + q) (r + w)
⟨_⊎_⟩ {p} {q} {r} {w} (f ⇆ f♯) (g ⇆ g♯) = mp ⇆ md
    where mp : position (p + q) → position (r + w)
          mp = map f g
          md : (fromPos : position (p + q)) → direction (r + w) (mp fromPos) → direction (p + q) fromPos
          md (inj₁ x) d = f♯ x d
          md (inj₂ y) d = g♯ y d
infixl 30 ⟨_⊎_⟩

-- Generalization of the coproduct (_+_).
-- Page 31 in the book.
ΣPoly : Σ[ indexType ∈ Set ] (indexType → Polynomial) → Polynomial
ΣPoly (indexType , generatePoly) = mkpoly pos dir
  where
    -- It is the positions of one of the polynomials
    pos : Set 
    pos = Σ[ index ∈ indexType ] (position (generatePoly index))

    -- It is the direction of the polynomial for the position
    dir : pos → Set
    dir (index , positionAtIndex) = direction (generatePoly index) positionAtIndex