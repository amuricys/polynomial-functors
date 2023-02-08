{-# OPTIONS --cubical #-}

module CubicalPoly.Category where

open import Level
open import Cubical.Core.Everything
open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Limits.Terminal
open import Cubical.Foundations.Isomorphism

hSetZero : Type₁
hSetZero = hSet ℓ-zero

record Polynomial : Type₁ where
    constructor MkPolynomial
    field
        position : Type -- hSetZero
        positionIsHSet : isSet position

        direction : position -> Type -- hSetZero
        directionIsHSet : (p : position) -> isSet (direction p)

PolyAsSigma : Type₁
PolyAsSigma = Σ[ position ∈ Type ] 
    (Σ[ positionIsHSet ∈ isSet position ]
    (Σ[ direction ∈ (position → Type) ]
    ((p : position) -> isSet (direction p))))

polyToSigma : Polynomial -> PolyAsSigma
polyToSigma (MkPolynomial position positionIsHSet direction directionIsHSet) 
    = position , ( positionIsHSet , (direction , directionIsHSet))

sigmaToPoly : PolyAsSigma -> Polynomial
sigmaToPoly (position , positionIsHSet , direction , directionIsHSet) = MkPolynomial position positionIsHSet direction directionIsHSet

isoPolySigma : Iso Polynomial PolyAsSigma
isoPolySigma = iso polyToSigma sigmaToPoly (λ b → refl) λ a -> refl

isSetSigma : isSet PolyAsSigma
isSetSigma = isSetΣ {!   !} 
    λ position -> isSetΣ (isSetIsSet {position}) 
    λ isSetPosition → isSetΣ {!   !}
    λ direction -> {! !}

    where
        isSetIsSet : {A : Type} -> isSet (isSet A)
        isSetIsSet = {!   !}


polyIsSet : isSet Polynomial
polyIsSet = isOfHLevelRetractFromIso 2 isoPolySigma isSetSigma

record Arrow (from to : Polynomial) : Type where
    constructor MkArrow
    open Polynomial
    field
        mapPosition : position from -> position to
        mapDirection : (fromPos : position from) -> direction to (mapPosition fromPos) -> direction from fromPos

data Hej : Type where
    ttt : Hej

ArrowAsSigma : Polynomial -> Polynomial -> Type
ArrowAsSigma A B = Σ[ mapPosition ∈ (Polynomial.position A -> Polynomial.position B) ] 
    ((fromPos : Polynomial.position A) -> Polynomial.direction B (mapPosition fromPos) -> Polynomial.direction A fromPos)
    
sigmaToArrow : {A B : Polynomial} -> ArrowAsSigma A B -> Arrow A B
sigmaToArrow (mapPosition , mapDirection) = MkArrow mapPosition mapDirection

arrowToSigma : {A B : Polynomial} -> Arrow A B -> ArrowAsSigma A B
arrowToSigma  (MkArrow mapPosition mapDirection) = mapPosition , mapDirection

isoArrowSigma : {A B : Polynomial} -> Iso (Arrow A B) (ArrowAsSigma A B)
isoArrowSigma = iso arrowToSigma sigmaToArrow (λ b → refl) (λ a → refl)

isSetArrowSigma : {A B : Polynomial} -> isSet (ArrowAsSigma A B)
isSetArrowSigma {B = B} = isSetΣ (isSetΠ (λ x → Polynomial.positionIsHSet B)) λ posMap -> {!   !}

arrowIsSet : {A B : Polynomial} -> isSet (Arrow A B)
arrowIsSet {A = A} {B = B}= isOfHLevelRetractFromIso 2 isoArrowSigma (isSetArrowSigma {A} {B})

IdArrow : {A : Polynomial} -> Arrow A A
IdArrow = MkArrow  (\x -> x) (λ fromPos toDir → toDir)

variable
    A B C : Polynomial

_∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
f ∘ g = λ x -> f (g x)

compose : {x y z : Polynomial} -> Arrow x y -> Arrow y z -> Arrow x z
compose (MkArrow bToCPos cToBDir) (MkArrow aToBPos bToADir) = MkArrow (λ z → aToBPos (bToCPos z)) λ fromPos z → cToBDir fromPos (bToADir (bToCPos fromPos) z) -- MkArrow (bToCPos ∘ aToBPos) (λ fromPos z → bToADir fromPos (cToBDir (aToBPos fromPos) z))  -- Can be autosolved.

Poly : Category (Level.suc 0ℓ) 0ℓ
Poly = record
    { ob = Polynomial
    ; Hom[_,_] = Arrow
    ; id = IdArrow
    ; _⋆_ = compose
    ; ⋆IdL = \f -> refl
    ; ⋆IdR = \f -> refl
    ; ⋆Assoc = λ f g h → refl
    ; isSetHom = arrowIsSet
    }

data True : Type where
    tt : True

data False : Type where

Zero : Polynomial
Zero = MkPolynomial False (λ x ()) (λ ()) λ ()

arrowFromZero : (p : Polynomial) -> Arrow Zero p
arrowFromZero p = MkArrow (λ ()) (λ ())

isZeroInitial : isInitial Poly Zero
isZeroInitial p = arrowFromZero p , λ {(MkArrow mapPosition mapDirection) → {!  !}}

-- arrowEqual : {A B : Polynomial} -> (f g : Arrow A B) -> (p : Arrow.mapPosition f ≡ Arrow.mapPosition g) -> (Arrow.mapDirection f) ≡ (Arrow.mapDirection g) -> f ≡ g
arrowEqual : {A B : Polynomial} -> {!   !}
arrowEqual = {!   !}

polyHasInitial : hasInitialOb Poly
polyHasInitial = Zero , isZeroInitial

isContrTrue : isContr True
isContrTrue = tt , λ {tt → refl}

isSetTrue : isSet True
isSetTrue = isContr→isOfHLevel 2 isContrTrue

One : Polynomial
One = MkPolynomial True isSetTrue (λ tt → False) (λ p x ())

arrowToOne : (p : Polynomial) -> Arrow p One
arrowToOne p = MkArrow (λ {x → tt}) λ {fromPos ()}

isOneFinal : isFinal Poly One
isOneFinal p = {!   !}

polyHasFinal : hasFinalOb Poly
polyHasFinal = One , isOneFinal