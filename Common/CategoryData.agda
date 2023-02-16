{-# OPTIONS --cubical #-}


module Common.CategoryData where

import Agda.Builtin.Nat as N

data True : Set where
    tt : True
    -- slets gooo
    
data False : Set where

data Either A B : Set where
    inL : A -> Either A B
    inR : B -> Either A B

data And A B : Set where
    and : A -> B -> And A B

uncurry : {A B C : Set} -> (A -> B -> C) -> (And A B -> C)
uncurry f (and a b) = f a b

data List A : Set where
    [] : List A
    _::_ : A -> List A -> List A

id : {A : Set} -> A -> A
id x = x

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = λ x -> f (g x)

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

compose : Arrow B C -> Arrow A B -> Arrow A C
compose (MkArrow bToCPos cToBDir) (MkArrow aToBPos bToADir) = MkArrow (bToCPos ∘ aToBPos) (λ fromPos z → bToADir fromPos (cToBDir (aToBPos fromPos) z))

_*_ : Arrow B C -> Arrow A B -> Arrow A C
_*_ = compose

-- Zero polynomial: p(y) = 0
Zero : Polynomial
Zero = MkPolynomial False (λ ())

arrowFromZero : {p : Polynomial} -> Arrow Zero p
arrowFromZero {p} = MkArrow (λ ()) (λ ())

-- One polynomial: p(y) = 1
One : Polynomial
One = MkPolynomial True (λ tt → False)

arrowToOne : (p : Polynomial) -> Arrow p One
arrowToOne p = MkArrow (λ {x → tt}) λ {fromPos ()}

_+_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA + MkPolynomial posB dirB = MkPolynomial (Either posA posB) (λ {(inL posA) → dirA posA
                                                                                    ; (inR posB) → dirB posB})

-- Product between two polynomials.
-- Pair of position. Each pair of positions has one direction, either from the left or the right polynomial.
_×_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA × MkPolynomial posB dirB = MkPolynomial (And posA posB) \{(and posA posB) → Either (dirA posA) (dirB posB)}

-- Tensor between two polynomials. Parallel product.
-- Pair of position. Each pair of position has one direction for each component.
_⊗_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA ⊗ MkPolynomial posB dirB = MkPolynomial (And posA posB) (λ {(and posA posB) → And (dirA posA) (dirB posB)})

-- Unit for tensor is Y. 1 position with 1 direction.
Y : Polynomial
Y = MkPolynomial True (λ _ → True)

-- Composition of polynomials (composition of polynomial functors, which happen to be new polynomial functor!).
_◂_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA ◂ MkPolynomial posB dirB = MkPolynomial ((i : posA) -> (dirA i) -> posB) (λ pos → (p : posA) -> (d : dirA p) -> dirB (pos p d))

-- Unit for composition is also Y.
Identity : Polynomial
Identity = Y

compositePower : Polynomial -> N.Nat -> Polynomial
compositePower p N.zero = Identity
compositePower p (N.suc n) = p ◂ (compositePower p n) 
