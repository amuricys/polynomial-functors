{-# OPTIONS --cubical #-}


module Common.CategoryData where

import Agda.Builtin.Nat as N
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Bool
-- open import 
open import Function
open import Cubical.Data.Sigma.Properties

record Polynomial : Set₁ where
    constructor MkPolynomial
    field
        position : Set
        direction : position -> Set

record Arrow (from to : Polynomial) : Set where
    -- constructor MkArrow
    constructor _⇄_
    open Polynomial
    field
        mapPosition : position from -> position to
        mapDirection : (fromPos : position from) -> direction to (mapPosition fromPos) -> direction from fromPos

variable
    A B C D : Polynomial

-- | For each polynomial we have the identity arrow.
-- | Positions are mapped to itself. The direction is taken as itself.
idArrow : Arrow A A
idArrow = id ⇄ λ _ → id

_∘p_ : Arrow B C -> Arrow A B -> Arrow A C
_∘p_ (bToCPos ⇄ cToBDir) (aToBPos ⇄ bToADir) = (bToCPos ∘ aToBPos) ⇄ (λ fromPos z → bToADir fromPos (cToBDir (aToBPos fromPos) z))

-- Zero polynomial: p(y) = 0
Zero : Polynomial
Zero = MkPolynomial ⊥ (λ ())

arrowFromZero : {p : Polynomial} -> Arrow Zero p
arrowFromZero {p} = (λ ()) ⇄ (λ ())

-- One polynomial: p(y) = 1
One : Polynomial
One = MkPolynomial ⊤ (λ {tt → ⊥})

arrowToOne : {p : Polynomial} -> Arrow p One
arrowToOne = (λ _ → tt) ⇄ λ {_ ()}

-- Constant polynomial: p(y) = A
Constant : {A : Set} -> Polynomial
Constant {A} = MkPolynomial A (λ _ → ⊥)

ex : Polynomial
ex = MkPolynomial Bool λ {false → Bool
                        ; true → ⊤}

f1 : ⊤ -> Bool
f1 _ = true

f2 : ⊤ -> Bool
f2 _ = false

-- Plug in a set: say you have p(y) = y^2 + 3. apply p 2 should return 2^2 + 3 ≅ 7
-- This is the action on objects (sets) of polynomials! They're (endo)functors after all.
apply : Polynomial → Set → Set
apply (MkPolynomial position direction) Y = Σ position λ x → (direction x → Y)

some : apply ex ⊤
some = false , (λ{ false → tt
                 ; true → tt })

some2 : apply ex ⊤
some2 = true , id

-- Plug in a function: say you have p(y) = y^2 + 3 and f : 2 → 3. applyFn p f should return a function from 
-- the type 2^2 + 3 ≅ 7 to the type 3^2 + 3 ≅ = 12. This is the action on morphisms (functions) of polynomials.
applyFn : {A B : Set} -> (p : Polynomial) -> (A -> B) -> (apply p A) -> (apply p B)
applyFn (MkPolynomial position direction) f (fst , snd) = fst , λ x → f (snd x)

_+_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA + MkPolynomial posB dirB = MkPolynomial (posA ⊎ posB) [ dirA , dirB ]
                                                                                    

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
 
fromArrowInPolyToFunctionBetweenAppliedPolys : {A B : Polynomial} {S : Set} -> Arrow A B -> apply A S -> apply B S
fromArrowInPolyToFunctionBetweenAppliedPolys {(MkPolynomial pos dir)} {B} (mapPosition ⇄ mapDirection) (f , s) =
  mapPosition f , λ {x₁ → s (mapDirection f x₁)}

enclose : Polynomial -> Set
enclose p = Arrow p Y


