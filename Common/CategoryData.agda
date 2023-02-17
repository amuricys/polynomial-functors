{-# OPTIONS --cubical #-}


module Common.CategoryData where

import Agda.Builtin.Nat as N
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Function

record Polynomial : Set₁ where
    constructor MkPolynomial
    field
        position : Set
        direction : position -> Set

record Arrow (from to : Polynomial) : Set where
    constructor MkArrow
    open Polynomial
    field
        mapPosition : position from -> position to
        mapDirection : (fromPos : position from) -> direction to (mapPosition fromPos) -> direction from fromPos

variable
    A B C D : Polynomial

-- | For each polynomial we have the identity arrow.
-- | Positions are mapped to itself. The direction is taken as itself.
idArrow : Arrow A A
idArrow = MkArrow id (λ fromPos toDir → toDir)

_∘p_ : Arrow B C -> Arrow A B -> Arrow A C
_∘p_ (MkArrow bToCPos cToBDir) (MkArrow aToBPos bToADir) = MkArrow (bToCPos ∘ aToBPos) (λ fromPos z → bToADir fromPos (cToBDir (aToBPos fromPos) z))

-- Zero polynomial: p(y) = 0
Zero : Polynomial
Zero = MkPolynomial ⊥ (λ ())

arrowFromZero : {p : Polynomial} -> Arrow Zero p
arrowFromZero {p} = MkArrow (λ ()) (λ ())

-- One polynomial: p(y) = 1
One : Polynomial
One = MkPolynomial ⊤ (λ tt → ⊥)

arrowToOne : (p : Polynomial) -> Arrow p One
arrowToOne p = MkArrow (λ {x → tt}) λ {fromPos ()}

-- Constant polynomial: p(y) = A
Constant : {A : Set} -> Polynomial
Constant {A} = MkPolynomial A (λ _ → ⊥)

_+_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA + MkPolynomial posB dirB = MkPolynomial (posA ⊎ posB) (λ {(inj₁ posA) → dirA posA
                                                                                    ; (inj₂ posB) → dirB posB})
                                                                                    

-- Product between two polynomials.
-- Pair of position. Each pair of positions has one direction, either from the left or the right polynomial.
_*_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA * MkPolynomial posB dirB = MkPolynomial (posA × posB) \{ (posA , posB)→ (dirA posA) ⊎ (dirB posB)}

-- Tensor between two polynomials. Parallel product.
-- Pair of position. Each pair of position has one direction for each component.
_⊗_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA ⊗ MkPolynomial posB dirB = MkPolynomial (posA × posB) (λ {(posA , posB) → (dirA posA) × (dirB posB)})

-- Unit for tensor is Y. 1 position with 1 direction.
Y : Polynomial
Y = MkPolynomial ⊤ (λ _ → ⊤)

-- Composition of polynomials (composition of polynomial functors, which happen to be new polynomial functor!).
_◂_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA ◂ MkPolynomial posB dirB = MkPolynomial ((i : posA) -> (dirA i) -> posB) (λ pos → (p : posA) -> (d : dirA p) -> dirB (pos p d))

-- Unit for composition is also Y.
Identity : Polynomial
Identity = Y

compositePower : Polynomial -> N.Nat -> Polynomial
compositePower p N.zero = Identity
compositePower p (N.suc n) = p ◂ (compositePower p n) 
