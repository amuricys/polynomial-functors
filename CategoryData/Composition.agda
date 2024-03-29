{-# OPTIONS --without-K #-}

module CategoryData.Composition where

open import CategoryData.Polynomial
open import CategoryData.Lens
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

infixl 32 _◂_

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
⟨_◂_⟩ : {p q r w : Polynomial} → Lens p r → Lens q w → Lens (p ◂ q) (r ◂ w)
⟨_◂_⟩ {p} {q} {r} {w} (f ⇆ f♯) (g ⇆ g♯) = mapPos ⇆ mapDir
  where mapPos : position (p ◂ q) → position (r ◂ w)
        mapPos (posP , dirPToPosQ) = f posP , λ a' → (g ∘ dirPToPosQ) (f♯ posP a')
        mapDir : (fromPos : position (p ◂ q)) → direction (r ◂ w) (mapPos fromPos) → direction (p ◂ q) fromPos
        mapDir (posP , dirPToPosQ) (dirR , dirW) = (f♯ posP dirR) , g♯ (dirPToPosQ (f♯ posP dirR)) dirW
infixl 28 ⟨_◂_⟩

speedup◂ : {p : Polynomial} {S : Set} → Lens (selfMonomial S) p → Lens (selfMonomial S) (p ◂ p)
speedup◂ {p} {S} l = dup ∘ₚ fixState
  where dup : Lens ((selfMonomial S) ◂ (selfMonomial S)) (p ◂ p)
        dup = ⟨ l ◂ l ⟩
        fixState : Lens (selfMonomial S) (selfMonomial S ◂ selfMonomial S)
        fixState = (λ s₀ → s₀ , λ s₁ → s₁) ⇆ λ { s₀ (s₁ , s₂) → s₂ } 