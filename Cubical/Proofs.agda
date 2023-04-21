{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Proofs where

open import CategoryData.Everything
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
open import Data.Product hiding (Σ-syntax)
open import Cubical.ArrowEquals

------- Categorical axioms
---------------------------------------
composeLeftIdentity : {B C : Polynomial} → (bToC : Arrow B C) → idArrow ∘ₚ bToC ≡ bToC
composeLeftIdentity (_ ⇄ _) = refl

composeRightIdentity :{B C : Polynomial} → (cToB : Arrow C B) → cToB ∘ₚ idArrow ≡ cToB
composeRightIdentity (_ ⇄ _) = refl

composeIsAssoc : ∀ {A B C D} → {f : Arrow A B} {g : Arrow B C} {h : Arrow C D} → ((h ∘ₚ g) ∘ₚ f) ≡ (h ∘ₚ (g ∘ₚ f))
composeIsAssoc = refl
---------------------------------------


------- Helpers idk what to do with
---------------------------------------
-- Got from here https://www.cse.chalmers.se/~abela/bigproof17/CubicalSolution.agda
-- trans : ∀{a}{A : Set a} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
-- trans {x = x} p q = drive (λ i → x ≡ q i) p
-- subst B p pa = transport (λ i → B (p i)) pa

transitivity : ∀ {a} {A : Set a} {x y z : A} (p : x ≡ y) → (q : y ≡ z) → x ≡ z
transitivity {x = x} p q = subst (_≡_ x) q p

-- We want B to be explicit in subst
-- subst : (B : A → Type ℓ') (p : x ≡ y) → B x → B y
-- subst B p pa = transport (λ i → B (p i)) pa

equiv-resp : {A B C : Polynomial} {f h : Arrow B C} {g i : Arrow A B} → f ≡ h → g ≡ i → (f ∘ₚ g) ≡ (h ∘ₚ i)
equiv-resp  p q ii = (p ii) ∘ₚ (q ii)

fromFalseFunctionsEqual : {A : Type} (f : ⊥ → A) → (g : ⊥ → A) → f ≡ g
fromFalseFunctionsEqual f g = funExt λ {()}

-- fromFalseFunctionsEqualAny : {A B : Type} (f : ⊥ → A) → (g : ⊥ → B) → f ≡ g
-- fromFalseFunctionsEqualAny f g = {!   !}

------- Helper conversions and isomorphism between converted representations
---------------------------------------

isoArrowSigma : {A B : Polynomial} → Iso (Arrow A B) (ArrowAsSigma A B)
isoArrowSigma = iso arrowToSigma sigmaToArrow (λ b → refl) (λ a → refl)
---------------------------------------

------- Proofs that two arrows are equal, or characterization of equality between arrows
---------------------------------------
arrowSigmasEqual : {p q : Polynomial} {f g : Arrow p q}
    → (mapPosEq : Arrow.mapPosition f ≡ Arrow.mapPosition g)
    → transport -- Basically "assuming map on positions is equal, then proof that map on directions is equal"
            (λ i →
                (fromPos : Polynomial.position p) →
                Polynomial.direction q (mapPosEq i fromPos) →
                Polynomial.direction p fromPos)
            (Arrow.mapDirection f)
            ≡ Arrow.mapDirection g
    → arrowToSigma f ≡ arrowToSigma g
arrowSigmasEqual {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq = ΣPathTransport→PathΣ (arrowToSigma f) (arrowToSigma g) (mapPosEq , mapDirEq)

arrowsEqual : {p q : Polynomial} {f g : Arrow p q}
    → (mapPosEq : Arrow.mapPosition f ≡ Arrow.mapPosition g)
    → transport -- Basically "assuming map on positions is equal, then proof that map on directions is equal"
            (λ i →
                (fromPos : Polynomial.position p) →
                Polynomial.direction q (mapPosEq i fromPos) →
                Polynomial.direction p fromPos)
            (Arrow.mapDirection f)
            ≡ Arrow.mapDirection g
    → f ≡ g
arrowsEqual {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq i = sigmaToArrow (arrowSigmasEqual {f = f} {g = g} mapPosEq mapDirEq i)

open Arrow
open Polynomial

-- X : {p q : Polynomial} → Set
-- X {p} {q} = position p → position q

-- A : {p q : Polynomial} → X {p} {q} → Set
-- A {p} {q} _ = position p

-- B : {p q : Polynomial} → (x : X {p} {q}) → A {p} {q} x → Type
-- B {p} {q} h i = direction q (h i) → direction p i

-- Π : {p q : Polynomial} → X {p} {q} → Type
-- Π {p} {q} = \ (x : X {p} {q}) → (a : A {p} {q} x) → B {p} {q} x a

-- B̂ : {p q : Polynomial} → Σ (X {p} {q}) (A {p} {q}) → Type
-- B̂ {p} {q} (w1 , w2) = B {p} {q} w1 w2


-- transportDep : {p q : Polynomial} {(f ⇄ f♯) (g ⇄ g♯) : Arrow p q} 
--   → (fn : (a : A {p} {q} f) → B {p} {q} f a) 
--   → (pr : f ≡ g) 
--   → (a : A {p} {q} g) → let
--   pairEq : ∀ {one two } → (one , a) ≡ (two , subst (A {p} {q}) (sym pr) a)
--   pairEq = {!   !}
--   in
--   (subst (Π {p} {q}) pr fn a ≡ subst (B̂ {p} {q}) (sym (pairEq {{!   !}} {{!   !}})) (fn (subst (A {p} {q}) (sym pr) a)))
-- transportDep {p} {q} pr f = {!  subst Π  !}

-- arrowsEqual2 : {p q : Polynomial} {f g : Arrow p q}
--     → (mapPosEq : mapPosition f ≡ mapPosition g)
--     → ((x : position p) → (y : direction q (mapPosition f x)) → mapDirection f x y ≡ mapDirection g x (subst (λ mapPos → direction q (mapPos x)) mapPosEq y) ) -- (subst (λ mapPos → direction q (mapPos x)) mapPosEq y)
--     → f ≡ g
-- arrowsEqual2 a b = arrowsEqual a (funExt λ x → funExt λ y → {! !}) -- λ i → transp {!   !} i {!   !})

arrowSigmasEqual3 : {p q : Polynomial} {f g : Arrow p q}
    → (mapPosEq : Arrow.mapPosition f ≡ Arrow.mapPosition g)
    → ((x : position p) → (y : direction q (mapPosition g x)) → mapDirection f x  (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) ≡ mapDirection g x y)
    → arrowToSigma f ≡ arrowToSigma g
arrowSigmasEqual3 {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq = ΣPathTransport→PathΣ (arrowToSigma f) (arrowToSigma g) (mapPosEq , funExt λ x  → funExt λ y → transitivity (lemma x y) (mapDirEq x y))
  where
    lemma : (x : position p) → (y : direction q (mapPosition g x)) → 
      (subst (λ h → (i : position p) → direction q (h i) → direction p i) mapPosEq (mapDirection f)) x y
      ≡
      mapDirection f x
      (subst (λ h → direction q (h x)) (sym mapPosEq) y)
    lemma x y i = transp (λ j → direction p (transp (λ _ → position p) (j ∨ i) x)) i ((mapDirection f (transp (λ _ → position p) i x) (transp (λ j → direction q (mapPosEq (~ j) (transp (λ _ → position p) (~ j ∨ i) x))) i0 y))) 


arrowsEqual3 : {p q : Polynomial} {f g : Arrow p q}
    → (mapPosEq : mapPosition f ≡ mapPosition g)
    → (
           (x : position p) → 
           (y : direction q (mapPosition g x)) → 
           mapDirection f x  
           (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) 
           ≡ 
           mapDirection g x y
        )
    → f ≡ g
arrowsEqual3 {f = f} {g = g} a b i = sigmaToArrow (arrowSigmasEqual3 {f = f} {g = g} a b i)


---------------------------------------

------- Proofs related to uniqueness of arrows from and to certain polynomials
---------------------------------------
arrowFromZeroUnique : {p : Polynomial} (f : Arrow 𝟘 p) → arrowFromZero ≡ f
arrowFromZeroUnique f = arrow≡ (funExt λ ()) (funExt λ ())

arrowToOneUnique : {p : Polynomial} (f : Arrow p 𝟙) →  arrowToOne ≡ f
arrowToOneUnique {p = p} f = arrow≡ refl (funExt λ x → funExt λ ())

---------------------------------------

------- Proofs related to plugging in 0
---------------------------------------
fromMapInDirectionToFunction : {p q : Polynomial} → (Polynomial.position p → Polynomial.position q) → p ⦅ ⊤ ⦆ → q ⦅ ⊤ ⦆
fromMapInDirectionToFunction {p} {q} f = \x →
  f (fst x) , λ _ → tt

fromFunctionToMapOnPositions : {p q : Polynomial} → (p ⦅ ⊤ ⦆ → q ⦅ ⊤ ⦆) → (Polynomial.position p → Polynomial.position q)
fromFunctionToMapOnPositions {p@(MkPoly pos dir)} {q} f = \x → let
  y : q ⦅ ⊤ ⦆
  y = f (x , λ x₁ → tt)
  in
  fst y

plugIn1IsoToMapPosition : {p q : Polynomial} → Iso (p ⦅ ⊤ ⦆ → q ⦅ ⊤ ⦆) (Polynomial.position p → Polynomial.position q)
plugIn1IsoToMapPosition = iso fromFunctionToMapOnPositions fromMapInDirectionToFunction (λ b → refl) (λ a → refl)

-- Proposition Not sure if this maybe is so similar
-- Proposition 3.40 in the book. (page 85)
enclosePoly≡depFuncToDirections : {p : Polynomial} → enclose p ≡ ((i : Polynomial.position p) → Polynomial.direction p i)
enclosePoly≡depFuncToDirections = isoToPath isoEnclosePolydepFuncToDirections
  where

    isoEnclosePolydepFuncToDirections : {p : Polynomial} → Iso (enclose p) ((i : Polynomial.position p) → Polynomial.direction p i)
    isoEnclosePolydepFuncToDirections = iso toRight toLeft (λ _ → refl) (λ _ → refl)
      where
        toRight : {p : Polynomial} → enclose p → ((i : Polynomial.position p) → Polynomial.direction p i)
        toRight (mapPosition ⇄ mapDirection) pos = mapDirection pos tt

        toLeft : {p : Polynomial} → ((i : Polynomial.position p) → Polynomial.direction p i) → enclose p
        toLeft p1 = (λ x → tt) ⇄ λ fromPos x → p1 fromPos

---------------------------------------


------- Specific arrow equalities
---------------------------------------
pwiseToExt : {A B : Set} {f g : A → B} → ({x : A} → f x Eq.≡ g x) → f ≡ g
pwiseToExt {A = A} {f = f} {g = g} p = let
  yaaa : {x : A} → f x ≡ g x
  yaaa = ptoc p
  in
  funExt (λ x → yaaa)

positionArrowsEqual : {A B : Polynomial} → {f g : Arrow A B} → f ≡ g → Arrow.mapPosition f ≡ Arrow.mapPosition g
positionArrowsEqual p i = Arrow.mapPosition (p i)

positionArrowsEqualPwise : {A B : Polynomial} →  {f g : Arrow A B} {z : Polynomial.position A} → f ≡ g → Arrow.mapPosition f z ≡ Arrow.mapPosition g z
positionArrowsEqualPwise {z = z} p i = let
  posEq = positionArrowsEqual p i
  in posEq z

positionArrowsEqualPwiseEq : {A B : Polynomial} {f g : Arrow A B} →
      f ≡ g →
      {x : Polynomial.position A} →
      Arrow.mapPosition f x Eq.≡ Arrow.mapPosition g x
positionArrowsEqualPwiseEq p = ctop (positionArrowsEqualPwise p)
--  
-- Proof that for any polynomal p with index set I, p(1) ≡ I
-- Proposition 2.43 in the book
I≡pOfOne : {A : Polynomial} → A ⦅ ⊤ ⦆ ≡ Polynomial.position A
I≡pOfOne = isoToPath isoI≡pOfOne
  where
    isoI≡pOfOne : {A : Polynomial} → Iso (A ⦅ ⊤ ⦆) (Polynomial.position A)
    isoI≡pOfOne = iso toRight toLeft inv1 inv2
      where
        toRight : {A : Polynomial} →  A ⦅ ⊤ ⦆ → Polynomial.position A
        toRight = fst

        toLeft : {A : Polynomial} → Polynomial.position A → A ⦅ ⊤ ⦆ 
        toLeft x = x , λ x₁ → tt

        inv1 = λ b → refl
        inv2 = λ {(fst₁ , snd₁) → refl}

-- derivative : Polynomial → Polynomial
-- derivative (MkPoly pos dir) = MkPoly (Σ pos dir) (λ {(i , a) → {! dir i - a  !}})

  