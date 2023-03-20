{-# OPTIONS --cubical --allow-unsolved-metas #-}

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
open import Data.Product hiding (Σ-syntax)

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

-- fromFalseFunctionsEqualAny : {A B : Type} (f : ⊥ -> A) -> (g : ⊥ -> B) -> f ≡ g
-- fromFalseFunctionsEqualAny f g = {!   !}

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

open Arrow
open Polynomial

arrowsEqual2 : {p q : Polynomial} {f g : Arrow p q}
    -> (mapPosEq : mapPosition f ≡ mapPosition g)
    -> ((x : position p) -> (y : direction q (mapPosition f x)) -> mapDirection f x y ≡ mapDirection g x (subst (λ mapPos → direction q (mapPos x)) mapPosEq y) ) -- (subst (λ mapPos → direction q (mapPos x)) mapPosEq y)
    -> f ≡ g
arrowsEqual2 a b = arrowsEqual a (funExt λ x → funExt λ y → {! !}) -- λ i → transp {!   !} i {!   !})

arrowSigmasEqual3 : {p q : Polynomial} {f g : Arrow p q}
    -> (mapPosEq : Arrow.mapPosition f ≡ Arrow.mapPosition g)
    -> ((x : position p) -> (y : direction q (mapPosition g x)) -> mapDirection f x  (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) ≡ mapDirection g x y) -- mapDirection f x (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) ≡ mapDirection g x y  ) -- (subst (λ mapPos → direction q (mapPos x)) mapPosEq y)
    -> arrowToSigma f ≡ arrowToSigma g
arrowSigmasEqual3 {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq = ΣPathTransport→PathΣ (arrowToSigma f) (arrowToSigma g) (mapPosEq , funExt λ x  → funExt λ y → transitivity (lemma x y) (mapDirEq x y))  -- {! ΣPathTransport→PathΣ (arrowToSigma f) (arrowToSigma g) (mapPosEq , mapDirEq) !} -- ΣPathTransport→PathΣ (arrowToSigma f) (arrowToSigma g) (mapPosEq , mapDirEq)
  where
    lemma : (x : position p) -> (y : direction q (mapPosition g x)) -> transport
      (λ i →
         (mapPos : position p) →
         direction q (mapPosEq i mapPos) → direction p mapPos)
      (mapDirection f) x y
      ≡
      mapDirection f x
      (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y)
    lemma x y = {!  !}

arrowsEqual3 : {p q : Polynomial} {f g : Arrow p q}
    -> (mapPosEq : mapPosition f ≡ mapPosition g)
    -> ((x : position p) -> (y : direction q (mapPosition g x)) -> mapDirection f x  (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) ≡ mapDirection g x y) -- mapDirection f x (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) ≡ mapDirection g x y  ) -- (subst (λ mapPos → direction q (mapPos x)) mapPosEq y)
    -> f ≡ g
arrowsEqual3 {f = f} {g = g} a b i = sigmaToArrow (arrowSigmasEqual3 {f = f} {g = g} a b i)


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
fromMapInDirectionToFunction : {p q : Polynomial} -> (Polynomial.position p → Polynomial.position q) → apply p ⊤ → apply q ⊤
fromMapInDirectionToFunction {p} {q} f = \x ->
  f (fst x) , λ _ → tt

fromFunctionToMapOnDirections : {p q : Polynomial} -> (apply p ⊤ -> apply q ⊤) -> (Polynomial.position p → Polynomial.position q)
fromFunctionToMapOnDirections {p@(MkPolynomial pos dir)} {q} f = \x -> let
  y : apply q ⊤
  y = f (x , λ x₁ → tt)
  in
  fst y

plugIn1IsoToMapDirection : {p q : Polynomial} -> Iso (apply p ⊤ -> apply q ⊤) (Polynomial.position p → Polynomial.position q)
plugIn1IsoToMapDirection = iso fromFunctionToMapOnDirections fromMapInDirectionToFunction (λ b -> refl) (λ a → refl)

-- Proposition Not sure if this maybe is so similar
-- Proposition 3.40 in the book. (page 85)
enclosePoly≡depFuncToDirections : {p : Polynomial} -> enclose p ≡ ((i : Polynomial.position p) -> Polynomial.direction p i)
enclosePoly≡depFuncToDirections = isoToPath isoEnclosePolydepFuncToDirections
  where

    isoEnclosePolydepFuncToDirections : {p : Polynomial} -> Iso (enclose p) ((i : Polynomial.position p) -> Polynomial.direction p i)
    isoEnclosePolydepFuncToDirections = iso toRight toLeft (λ _ → refl) (λ _ → refl)
      where
        toRight : {p : Polynomial} -> enclose p → ((i : Polynomial.position p) -> Polynomial.direction p i)
        toRight (mapPosition ⇄ mapDirection) pos = mapDirection pos tt

        toLeft : {p : Polynomial} -> ((i : Polynomial.position p) -> Polynomial.direction p i) → enclose p
        toLeft p1 = (λ x → tt) ⇄ λ fromPos x → p1 fromPos

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
--  
-- Proof that for any polynomal p with index set I, p(1) ≡ I
-- Proposition 2.43 in the book
I≡pOfOne : {A : Polynomial} → apply A ⊤ ≡ Polynomial.position A
I≡pOfOne = isoToPath isoI≡pOfOne
  where
    isoI≡pOfOne : {A : Polynomial} → Iso (apply A ⊤) (Polynomial.position A)
    isoI≡pOfOne = iso toRight toLeft inv1 inv2
      where
        toRight : apply A ⊤ → Polynomial.position A
        toRight = fst

        toLeft : Polynomial.position A → apply A ⊤ 
        toLeft x = x , λ x₁ → tt

        inv1 = λ b → refl
        inv2 = λ {(fst₁ , snd₁) → refl}

-- derivative : Polynomial → Polynomial
-- derivative (MkPolynomial pos dir) = MkPolynomial (Σ pos dir) (λ {(i , a) → {! dir i - a  !}})

