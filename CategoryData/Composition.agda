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
_◂_ : Polynomial → Polynomial → Polynomial
p ◂ q = MkPoly pos dir
  where
    module p = Polynomial p
    module q = Polynomial q

    pos : Set
    pos = (Σ[ i ∈ p.position ] (p.direction i → q.position))

    dir : pos → Set
    dir (i , j) = Σ[ a ∈ p.direction i ] q.direction (j a)
infixl 27 _◂_

compositionUnit : Polynomial
compositionUnit = Y

compositePower : Polynomial → ℕ → Polynomial
compositePower p zero = compositionUnit
compositePower p (suc n) = p ◂ (compositePower p n) 

~ᴿ : {c : Polynomial} → Arrow c (c ◂ Y)
~ᴿ =  (_, const tt) ⇄ λ _ → proj₁

~ᴸ : {c : Polynomial} → Arrow c (Y ◂ c)
~ᴸ =  (λ x → tt , const x) ⇄ λ _ → proj₂

-- Apply arrows to both sides of the monoidal structure
⟨_◂_⟩ : {p q r s : Polynomial} → Arrow p r → Arrow q s → Arrow (p ◂ q) (r ◂ s)
⟨_◂_⟩ {p} {q} {r} {s} (f ⇄ f♯) (g ⇄ g♯) = mapPos ⇄ mapDir
  where mapPos : position (p ◂ q) → position (r ◂ s)
        mapPos (posP , dirPToPosQ) = f posP , g ∘ dirPToPosQ ∘ f♯ posP
        mapDir : (fromPos : position (p ◂ q)) → direction (r ◂ s) (mapPos fromPos) → direction (p ◂ q) fromPos
        mapDir (posP , dirPToPosQ) (dirR , dirS) = (f♯ posP dirR) , g♯ (dirPToPosQ (f♯ posP dirR)) dirS
infixl 28 ⟨_◂_⟩
