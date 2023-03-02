{-# OPTIONS --cubical #-}

module AgdaCategories.Gist where

open import Categories.Category
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming ( id to idN )
open import Categories.Category.Instance.Sets
open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality
open import Function
open import Data.Unit
open import Data.Empty
open import Level
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties
import Relation.Binary.PropositionalEquality as Eq

record Polynomial : Set₁ where
    constructor MkPolynomial
    field
        position : Set
        direction : position -> Set

record Arrow (from to : Polynomial) : Set where
    constructor _⇄_
    open Polynomial
    field
        mapPosition : position from -> position to
        mapDirection : (fromPos : position from) -> direction to (mapPosition fromPos) -> direction from fromPos

_∘p_ : {A B C : Polynomial} -> Arrow B C -> Arrow A B -> Arrow A C
_∘p_ (bToCPos ⇄ cToBDir) (aToBPos ⇄ bToADir) = (bToCPos ∘ aToBPos) ⇄ (λ fromPos z → bToADir fromPos (cToBDir (aToBPos fromPos) z))

equiv-resp : {A B C : Polynomial} {f h : Arrow B C} {g i : Arrow A B} → f ≡ h → g ≡ i → (f ∘p g) ≡ (h ∘p i)
equiv-resp  p q ii = (p ii) ∘p (q ii)

transitivity : ∀ {a} {A : Set a} {x y z : A} (p : x ≡ y) -> (q : y ≡ z) -> x ≡ z
transitivity {x = x} p q = subst (_≡_ x) q p

Poly : Category (Level.suc Level.zero) Level.zero Level.zero
Poly = record
    { Obj = Polynomial
    ; _⇒_ = Arrow
    ; _≈_ = _≡_
    ; id = id ⇄ λ _ → id
    ; _∘_ = _∘p_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = transitivity } -- subst (_≡_ x) q p }
    ; ∘-resp-≈ = equiv-resp
    }


ArrowAsSigma : Polynomial -> Polynomial -> Type
ArrowAsSigma A B = Σ[ mapPosition ∈ (Polynomial.position A -> Polynomial.position B) ] 
    ((fromPos : Polynomial.position A) -> Polynomial.direction B (mapPosition fromPos) -> Polynomial.direction A fromPos)
    
sigmaToArrow : {A B : Polynomial} -> ArrowAsSigma A B -> Arrow A B
sigmaToArrow (mapPosition , mapDirection) = mapPosition ⇄ mapDirection

arrowToSigma : {A B : Polynomial} -> Arrow A B -> ArrowAsSigma A B
arrowToSigma  (mapPosition ⇄ mapDirection) = mapPosition , mapDirection

isoArrowSigma : {A B : Polynomial} -> Iso (Arrow A B) (ArrowAsSigma A B)
isoArrowSigma = iso arrowToSigma sigmaToArrow (λ b → refl) (λ a → refl)
---------------------------------------

------- Proofs that two arrows are equal, or characterization of equality between arrows
---------------------------------------
arrowSigmasEqual : {p q : Polynomial} {f g : Arrow p q}
    -> (mapPosEq : Arrow.mapPosition f ≡ Arrow.mapPosition g)
    -> transport -- Basically "assuming map on positions is equal, then proof that map on directions is equal"
            (λ i →
                (fromPos : Polynomial.position p) →
                Polynomial.direction q (mapPosEq i fromPos) →
                Polynomial.direction p fromPos)
            (Arrow.mapDirection f)
            ≡ Arrow.mapDirection g
    -> arrowToSigma f ≡ arrowToSigma g
arrowSigmasEqual {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq = ΣPathTransport→PathΣ (arrowToSigma f) (arrowToSigma g) (mapPosEq , mapDirEq)

arrowsEqual : {p q : Polynomial} {f g : Arrow p q}
    -> (mapPosEq : Arrow.mapPosition f ≡ Arrow.mapPosition g)
    -> transport -- Basically "assuming map on positions is equal, then proof that map on directions is equal"
            (λ i →
                (fromPos : Polynomial.position p) →
                Polynomial.direction q (mapPosEq i fromPos) →
                Polynomial.direction p fromPos)
            (Arrow.mapDirection f)
            ≡ Arrow.mapDirection g
    -> f ≡ g
arrowsEqual {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq i = sigmaToArrow (arrowSigmasEqual {f = f} {g = g} mapPosEq mapDirEq i)
---------------------------------------

-- Plug in a set: say you have p(y) = y^2 + 3. applyPoly(2) should return 2^2 + 3 ≅ 7
apply : Polynomial → Set → Set
apply (MkPolynomial position direction) Y = Σ position λ x → (direction x → Y)

fromArrowInPolyToFunctionBetweenAppliedPolys : {A B : Polynomial} {S : Set} -> Arrow A B -> apply A S -> apply B S
fromArrowInPolyToFunctionBetweenAppliedPolys {(MkPolynomial pos dir)} {B} (mapPosition ⇄ mapDirection) (f , s) =
  mapPosition f , λ {x₁ → s (mapDirection f x₁)}

fromArrowInPolyToFunction2 : {A B : Polynomial} -> Arrow A B -> apply A ⊤ -> apply B ⊤
fromArrowInPolyToFunction2 {(MkPolynomial pos dir)} {B} (mapPosition ⇄ mapDirection) = \x → let
  positionAirquotes = fst x
  directionAirquoteslol = snd x
  in mapPosition positionAirquotes , λ {x₁ → directionAirquoteslol (mapDirection positionAirquotes x₁)}

appliedPolyArrowsEq2 : {A B : Polynomial} {f g : Arrow A B} -> f ≡ g -> fromArrowInPolyToFunction2 f ≡ fromArrowInPolyToFunction2 g
appliedPolyArrowsEq2 p i = fromArrowInPolyToFunction2 (p i)

appliedPolyArrowsEqPwise2 : {A B : Polynomial} {f g : Arrow A B} {z : apply A ⊤} → f ≡ g -> fromArrowInPolyToFunction2 f z ≡ fromArrowInPolyToFunction2 g z
appliedPolyArrowsEqPwise2 {z = z} p i = let
  posEq = appliedPolyArrowsEq2 p i
  in posEq z

appliedPolyArrowsEqPwiseEq2 : {A B : Polynomial}
      {f g : Arrow A B} →
      f ≡ g →
      {z : apply A ⊤} →
      fromArrowInPolyToFunction2 f z Eq.≡ fromArrowInPolyToFunction2 g z
appliedPolyArrowsEqPwiseEq2 p {z} = ctop (appliedPolyArrowsEqPwise2 {z = z} p)

-- -- Functor sending a polynomial to its set of positions "plugging in 1"
plugIn1 : Functor Poly (Sets Level.zero)
plugIn1 = record
    { F₀ = λ x → apply x ⊤
    ; F₁ = fromArrowInPolyToFunctionBetweenAppliedPolys
    ; identity = Eq.refl
    ; homomorphism = Eq.refl
    ; F-resp-≈ = appliedPolyArrowsEqPwiseEq2
    }

-- Fully faithful functor sending a set A to the constant polynomial Ay^0 = A
constantPolynomial : Functor (Sets Level.zero) Poly 
constantPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → ⊥
    ; F₁ = λ f → f ⇄ λ fromPos → id
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ p → arrowsEqual (funExt λ x → ptoc p) refl
    }

plugin1unit : NaturalTransformation idF (constantPolynomial ∘F plugIn1)
plugin1unit = record { 
    η = λ X → (λ x → {!   !} , λ _ → tt) ⇄ λ fromPos () ;
    commute = λ f@(mapDir ⇄ mapPos) -> λ i -> {!   !} ;
    sym-commute = λ f -> {!   !}
    }
