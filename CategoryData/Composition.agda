{-# OPTIONS --without-K #-}

module CategoryData.Composition where

open import CategoryData.Core
open import CategoryData.SimplePolynomials
open import Data.Product
open import Data.Unit
open import Data.Nat
open import Function

-- Composition of polynomials (remember, polynomials are ENDOfunctors so they compose 
-- to give a new polynomial functor!).
-- Proposition 5.2, page 158. Note: not same definition used. We here treat positions
-- as inhabitants of the same set, which makes a lot of proofs easier down the line.
pos : (p q : Polynomial) → Set
pos p q = (Σ[ i ∈ position p ] (direction p i → position q))

dir : (p q : Polynomial) → (posat : pos p q) → Set
dir p q (i , j) = Σ[ a ∈ direction p i ] direction q (j a)

_◂_ : Polynomial → Polynomial → Polynomial
p ◂ q = mkpoly (pos p q) (dir p q)

infixl 27 _◂_

compositionUnit : Polynomial
compositionUnit = Y

compositePower : Polynomial → ℕ → Polynomial
compositePower p zero = compositionUnit
compositePower p (suc n) = p ◂ (compositePower p n) 

~ᴿ : {c : Polynomial} → Lens c (c ◂ Y)
~ᴿ =  (_, const tt) ⇆ λ _ → proj₁

~ᴸ : {c : Polynomial} → Lens c (Y ◂ c)
~ᴸ =  (λ x → tt , const x) ⇆ λ _ → proj₂

-- Apply lenses to both sides of the monoidal structure
⟨_◂_⟩ : {p q r s : Polynomial} → Lens p r → Lens q s → Lens (p ◂ q) (r ◂ s)
⟨_◂_⟩ {p} {q} {r} {s} (f ⇆ f♯) (g ⇆ g♯) = mapPos ⇆ mapDir
  where mapPos : position (p ◂ q) → position (r ◂ s)
        mapPos (posP , dirPToPosQ) = f posP , g ∘ dirPToPosQ ∘ f♯ posP
        mapDir : (fromPos : position (p ◂ q)) → direction (r ◂ s) (mapPos fromPos) → direction (p ◂ q) fromPos
        mapDir (posP , dirPToPosQ) (dirR , dirS) = (f♯ posP dirR) , g♯ (dirPToPosQ (f♯ posP dirR)) dirS
infixl 28 ⟨_◂_⟩
