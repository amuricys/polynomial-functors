{-# OPTIONS --without-K #-}

module Common.CategoryData where

import Agda.Builtin.Nat as N
open import Agda.Builtin.Unit
open import Data.Empty
open import Data.Sum
open import Data.Product
open import Data.Bool
open import Function


record Polynomial : Set₁ where
    constructor MkPoly
    field
        position : Set
        direction : position → Set

record Arrow (from to : Polynomial) : Set where
    constructor _⇄_
    open Polynomial
    field
        mapPosition : position from → position to
        mapDirection : (fromPos : position from) → direction to (mapPosition fromPos) → direction from fromPos

-- | For each polynomial we have the identity arrow.
-- | Positions are mapped to itself. The direction is taken as itself.
idArrow : {A : Polynomial} → Arrow A A
idArrow = id ⇄ λ _ → id

_∘p_ : {A B C : Polynomial} → Arrow B C → Arrow A B → Arrow A C
_∘p_ (bToCPos ⇄ cToBDir) (aToBPos ⇄ bToADir) = (bToCPos ∘ aToBPos) ⇄ (λ fromPos z → bToADir fromPos (cToBDir (aToBPos fromPos) z))

-- Zero polynomial: p(y) = 0
Zero : Polynomial
Zero = MkPoly ⊥ (λ ())

arrowFromZero : {p : Polynomial} → Arrow Zero p
arrowFromZero {p} = (λ ()) ⇄ (λ ())

-- One polynomial: p(y) = 1
One : Polynomial
One = MkPoly ⊤ (λ {tt → ⊥})

arrowToOne : {p : Polynomial} → Arrow p One
arrowToOne = (λ _ → tt) ⇄ λ {_ ()}

-- Constant polynomial: p(y) = A
Constant : (A : Set) → Polynomial
Constant A = MkPoly A (λ _ → ⊥)

ex : Polynomial
ex = MkPoly Bool λ {false → Bool
                        ; true → ⊤}

f1 : ⊤ → Bool
f1 _ = true

f2 : ⊤ → Bool
f2 _ = false

-- Plug in a set: say you have p(y) = y^2 + 3. p ⦅ 2 ⦆ should return 2^2 + 3 ≅ 7
-- This is the action on objects (sets) of that polynomials perform as functors. They're (endo)functors after all.
_⦅_⦆ : Polynomial → Set → Set
_⦅_⦆ (MkPoly position direction) Y = Σ position λ x → (direction x → Y)

some : ex ⦅ ⊤ ⦆
some = false , (λ{ false → tt
                 ; true → tt })

some2 : ex ⦅ ⊤ ⦆
some2 = true , id

-- Plug in a function: say you have p(y) = y^2 + 3 and f : 2 → 3. applyFn p f should return a function from 
-- the type 2^2 + 3 ≅ 7 to the type 3^2 + 3 ≅ = 12. This is the action on morphisms (functions) that polynomials
-- perform as functors (they are endofunctors in Set after all)
applyFn : {A B : Set} → (p : Polynomial) → (A → B) → p ⦅ A ⦆ → p ⦅ B ⦆
applyFn (MkPoly position direction) f (fst , snd) = fst , λ x → f (snd x)

_+_ : Polynomial → Polynomial → Polynomial
MkPoly posA dirA + MkPoly posB dirB = MkPoly (posA ⊎ posB) [ dirA , dirB ]


-- Product between two polynomials.
-- Pair of position. Each pair of positions has one direction, either from the left or the right polynomial.
_*_ : Polynomial → Polynomial → Polynomial
MkPoly posA dirA * MkPoly posB dirB = MkPoly (posA × posB) \{ (posA , posB)→ (dirA posA) ⊎ (dirB posB)}

-- Tensor between two polynomials. Parallel product.
-- Pair of position. Each pair of position has one direction for each component.
_⊗_ : Polynomial → Polynomial → Polynomial
MkPoly posA dirA ⊗ MkPoly posB dirB = MkPoly (posA × posB) (λ {(posA , posB) → (dirA posA) × (dirB posB)})

-- Unit for tensor is Y. 1 position with 1 direction.
Y : Polynomial
Y = MkPoly ⊤ (λ _ → ⊤)

-- Composition of polynomials (composition of polynomial functors, which happen to be new polynomial functor!).
-- Proposition 5.2, page 158. Note: not same definition used.
_◂_ : Polynomial → Polynomial → Polynomial
p ◂ q = MkPoly pos dir
  where
    module p = Polynomial p
    module q = Polynomial q

    pos : Set
    pos = (Σ[ i ∈ p.position ] (p.direction i → q.position))

    dir : pos → Set
    dir (i , j) = Σ[ a ∈ p.direction i ] q.direction (j a)

-- Unit for composition is also Y.
Identity : Polynomial
Identity = Y

compositePower : Polynomial → N.Nat → Polynomial
compositePower p N.zero = Identity
compositePower p (N.suc n) = p ◂ (compositePower p n) 

fromArrowInPolyToFunctionBetweenAppliedPolys : {p q : Polynomial} {S : Set} → Arrow p q → p ⦅ S ⦆ → q ⦅ S ⦆
fromArrowInPolyToFunctionBetweenAppliedPolys {(MkPoly pos dir)} {B} (mapPosition ⇄ mapDirection) (f , s) =
  mapPosition f , λ {x₁ → s (mapDirection f x₁)}

enclose : Polynomial → Set
enclose p = Arrow p Y

monomial : (A B : Set) → Polynomial -- A*Y^B
monomial A B = MkPoly A (λ _ → B)

selfMonomial : Set → Polynomial -- S*Y^S
selfMonomial S = monomial S S

-- | A pure power summand.
purePower : Set → Polynomial
purePower power = MkPoly ⊤ λ _ → power

open Polynomial

-- Generalization of the product (_*_) poly.
ΠPoly : Σ[ indexType ∈ Set ] (indexType → Polynomial) → Polynomial
ΠPoly (indexType , generatePoly) = MkPoly pos dir
  where
    pos : Set
    pos = (index : indexType) → position (generatePoly index) -- It embeds all polynomial positions into one position

    dir : pos → Set
    dir pos = Σ[ index ∈ indexType ] direction (generatePoly index) (pos index) -- The direction is exactly one of the directions of all polynomials directions at that position

-- Generalization of the coproduct (_+_).
-- Page 31 in the book.
ΣPoly : Σ[ indexType ∈ Set ] (indexType → Polynomial) → Polynomial
ΣPoly (indexType , generatePoly) = MkPoly pos dir
  where
    pos : Set 
    pos = Σ[ index ∈ indexType ] (position (generatePoly index)) -- It is the positions of one of the polynomials

    dir : pos → Set
    dir (index , positionAtIndex) = direction (generatePoly index) positionAtIndex


-- Exponential object.
-- Theroem 4.27, page 130 in Poly book.
_^_ : (r : Polynomial) → (q : Polynomial) → Polynomial
_^_ r (MkPoly posQ dirQ) = ΠPoly (posQ , λ j → r ◂ (Y + Constant (dirQ j)))
