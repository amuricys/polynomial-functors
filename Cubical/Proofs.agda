{-# OPTIONS --cubical #-}

module Cubical.Proofs where

open import Common.CategoryData
open import Level
open import Agda.Builtin.Unit
open import Data.Empty
open import Cubical.Core.Everything
open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Categories.Limits.Terminal
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties


-- Categorical axioms
composeLeftIdentity : (bToC : Arrow B C) -> idArrow ∘p bToC ≡ bToC
composeLeftIdentity (MkArrow mapPosition mapDirection) = refl

composeRightIdentity : (cToB : Arrow C B) -> cToB ∘p idArrow ≡ cToB
composeRightIdentity (MkArrow mapPosition mapDirection) = refl

composeIsAssoc : ∀ {A B C D} -> {f : Arrow A B} {g : Arrow B C} {h : Arrow C D} -> ((h ∘p g) ∘p f) ≡ (h ∘p (g ∘p f))
composeIsAssoc = refl


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

ArrowAsSigma : Polynomial -> Polynomial -> Type
ArrowAsSigma A B = Σ[ mapPosition ∈ (Polynomial.position A -> Polynomial.position B) ] 
    ((fromPos : Polynomial.position A) -> Polynomial.direction B (mapPosition fromPos) -> Polynomial.direction A fromPos)
    
sigmaToArrow : {A B : Polynomial} -> ArrowAsSigma A B -> Arrow A B
sigmaToArrow (mapPosition , mapDirection) = MkArrow mapPosition mapDirection

arrowToSigma : {A B : Polynomial} -> Arrow A B -> ArrowAsSigma A B
arrowToSigma  (MkArrow mapPosition mapDirection) = mapPosition , mapDirection

isoArrowSigma : {A B : Polynomial} -> Iso (Arrow A B) (ArrowAsSigma A B)
isoArrowSigma = iso arrowToSigma sigmaToArrow (λ b → refl) (λ a → refl)

isContrTrue : isContr ⊤
isContrTrue = tt , λ {tt → refl}

isSetTrue : isSet ⊤
isSetTrue = isContr→isOfHLevel 2 isContrTrue

arrowSigmasEqual : {p q : Polynomial} {f g : Arrow p q}
    -> (mapPosEq : Arrow.mapPosition f ≡ Arrow.mapPosition g)
    -> transport -- Basically "assuming map on positions is equal, then proof that map on directions is equal"
            (λ i →
                (fromPos : Polynomial.position p) →
                Polynomial.direction q (mapPosEq i fromPos) →
                Polynomial.direction p fromPos)
            (snd (arrowToSigma f))
            ≡ snd (arrowToSigma g)
    -> arrowToSigma f ≡ arrowToSigma g
arrowSigmasEqual {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq = ΣPathTransport→PathΣ (arrowToSigma f) (arrowToSigma g) (mapPosEq , mapDirEq)

arrowsEqual : {p q : Polynomial} {f g : Arrow p q}
    -> (mapPosEq : Arrow.mapPosition f ≡ Arrow.mapPosition g)
    -> transport -- Basically "assuming map on positions is equal, then proof that map on directions is equal"
            (λ i →
                (fromPos : Polynomial.position p) →
                Polynomial.direction q (mapPosEq i fromPos) →
                Polynomial.direction p fromPos)
            (snd (arrowToSigma f))
            ≡ snd (arrowToSigma g)
    -> f ≡ g
arrowsEqual {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq i = sigmaToArrow (arrowSigmasEqual {f = f} {g = g} mapPosEq mapDirEq i)

arrowFromZeroUnique : {p : Polynomial} (f : Arrow Zero p) -> arrowFromZero ≡ f
arrowFromZeroUnique f = arrowsEqual (λ {i ()}) (funExt λ {()})

arrowToOneUnique : {p : Polynomial} (f : Arrow p One) ->  arrowToOne ≡ f
arrowToOneUnique {p = p} f = arrowsEqual mapPosEq (λ {i fromPos ()} )
    where
        isPropUnit : (x y : ⊤) -> x ≡ y
        isPropUnit tt tt = refl
        
        mapPosEq : (λ x → tt) ≡ (λ x → tt)
        mapPosEq = funExt λ x i → isPropUnit (Arrow.mapPosition f x) (Arrow.mapPosition (arrowToOne {p}) x) i
