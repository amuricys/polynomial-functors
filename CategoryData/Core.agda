{-# OPTIONS --without-K #-}

module CategoryData.Core where

open import Function

record Polynomial : Set₁ where
    constructor MkPoly
    field
        position : Set
        direction : position → Set
open Polynomial public

record Arrow (from to : Polynomial) : Set where
    constructor _⇄_
    open Polynomial
    field
        mapPosition : position from → position to
        mapDirection : (fromPos : position from) → direction to (mapPosition fromPos) → direction from fromPos
open Arrow public

-- | For each polynomial we have the identity arrow.
-- | Positions are mapped to itself. The direction is taken as itself.
idArrow : {A : Polynomial} → Arrow A A
idArrow = id ⇄ λ _ → id

-- | Composition of polynomials works as you would expect, with the care that ♯ are dependent.
-- | p  -- f -- > q -- g -- > r
-- |    <- f♯ ---   <- g♯ --- 
_∘ₚ_ : {A B C : Polynomial} → Arrow B C → Arrow A B → Arrow A C
_∘ₚ_ (f ⇄ f♯) (g ⇄ g♯) = (f ∘ g) ⇄ (λ fromPos z → g♯ fromPos (f♯ (g fromPos) z))