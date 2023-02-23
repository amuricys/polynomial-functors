{-# OPTIONS --cubical #-}

module Cubical.Proofs where

open import Common.CategoryData
open import Level
open import Agda.Builtin.Unit
open import Data.Empty
import Relation.Binary.PropositionalEquality as Eq
open import Cubical.Data.Equality using (ctop ; ptoc)
open import Cubical.Core.Everything
open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Limits.Terminal
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties

------- Categorical axioms
---------------------------------------
composeLeftIdentity : (bToC : Arrow B C) -> idArrow ∘p bToC ≡ bToC
composeLeftIdentity (_ ⇄ _) = refl

composeRightIdentity : (cToB : Arrow C B) -> cToB ∘p idArrow ≡ cToB
composeRightIdentity (_ ⇄ _) = refl

composeIsAssoc : ∀ {A B C D} -> {f : Arrow A B} {g : Arrow B C} {h : Arrow C D} -> ((h ∘p g) ∘p f) ≡ (h ∘p (g ∘p f))
composeIsAssoc = refl
---------------------------------------


------- Helpers idk what to do with
---------------------------------------
-- Got from here https://www.cse.chalmers.se/~abela/bigproof17/CubicalSolution.agda
-- trans : ∀{a}{A : Set a} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
-- trans {x = x} p q = drive (λ i → x ≡ q i) p
-- subst B p pa = transport (λ i → B (p i)) pa

transitivity : ∀ {a} {A : Set a} {x y z : A} (p : x ≡ y) -> (q : y ≡ z) -> x ≡ z
transitivity {x = x} p q = subst (_≡_ x) q p

-- We want B to be explicit in subst
-- subst : (B : A → Type ℓ') (p : x ≡ y) → B x → B y
-- subst B p pa = transport (λ i → B (p i)) pa

equiv-resp : {A B C : Polynomial} {f h : Arrow B C} {g i : Arrow A B} → f ≡ h → g ≡ i → (f ∘p g) ≡ (h ∘p i)
equiv-resp  p q ii = (p ii) ∘p (q ii)

fromFalseFunctionsEqual : {A : Type} (f : ⊥ -> A) -> (g : ⊥ -> A) -> f ≡ g
fromFalseFunctionsEqual f g = funExt λ {()}

------- Helper conversions and isomorphism between converted representations
---------------------------------------
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

------- Proofs related to uniqueness of arrows from and to certain polynomials
---------------------------------------
arrowFromZeroUnique : {p : Polynomial} (f : Arrow Zero p) -> arrowFromZero ≡ f
arrowFromZeroUnique f = arrowsEqual (λ {i ()}) (funExt λ {()})

arrowToOneUnique : {p : Polynomial} (f : Arrow p One) ->  arrowToOne ≡ f
arrowToOneUnique {p = p} f = arrowsEqual mapPosEq (λ {i fromPos ()} )
    where
        isPropUnit : (x y : ⊤) -> x ≡ y
        isPropUnit tt tt = refl
        
        mapPosEq : (λ x → tt) ≡ (λ x → tt)
        mapPosEq = funExt λ x i → isPropUnit (Arrow.mapPosition f x) (Arrow.mapPosition (arrowToOne {p}) x) i
---------------------------------------

------- Proofs related to plugging in 0
---------------------------------------
fromMapInDirectionToFunction : {p q : Polynomial} -> (Polynomial.position p → Polynomial.position q) → applyPoly p ⊤ → applyPoly q ⊤
fromMapInDirectionToFunction {p} {q} f = \x ->
  f (fst x) , λ _ → tt

fromFunctionToMapOnDirections : {p q : Polynomial} -> (applyPoly p ⊤ -> applyPoly q ⊤) -> (Polynomial.position p → Polynomial.position q)
fromFunctionToMapOnDirections {p@(MkPolynomial pos dir)} {q} f = \x -> let
  y : applyPoly q ⊤
  y = f (x , λ x₁ → tt)
  in
  fst y

plugIn1IsoToMapDirection : {p q : Polynomial} -> Iso (applyPoly p ⊤ -> applyPoly q ⊤) (Polynomial.position p → Polynomial.position q)
plugIn1IsoToMapDirection = iso fromFunctionToMapOnDirections fromMapInDirectionToFunction (λ b -> refl) (λ a → refl)
---------------------------------------


------- Specific arrow equalities
---------------------------------------
pwiseToExt : {A B : Set} {f g : A → B} -> ({x : A} → f x Eq.≡ g x) -> f ≡ g
pwiseToExt {A = A} {f = f} {g = g} p = let
  yaaa : {x : A} → f x ≡ g x
  yaaa = ptoc p
  in
  funExt (λ x → yaaa)

positionArrowsEqual : {f g : Arrow A B} -> f ≡ g -> Arrow.mapPosition f ≡ Arrow.mapPosition g
positionArrowsEqual p i = Arrow.mapPosition (p i)

positionArrowsEqualPwise : {f g : Arrow A B} {z : Polynomial.position A} → f ≡ g -> Arrow.mapPosition f z ≡ Arrow.mapPosition g z
positionArrowsEqualPwise {z = z} p i = let
  posEq = positionArrowsEqual p i
  in posEq z

positionArrowsEqualPwiseEq : {A B : Polynomial} {f g : Arrow A B} →
      f ≡ g →
      {x : Polynomial.position A} →
      Arrow.mapPosition f x Eq.≡ Arrow.mapPosition g x
positionArrowsEqualPwiseEq p = ctop (positionArrowsEqualPwise p)