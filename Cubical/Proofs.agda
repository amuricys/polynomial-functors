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
open import Data.Sum
open import Cubical.PolynomialEquals
open import Function

------- Categorical axioms
---------------------------------------
composeLeftIdentity : {B C : Polynomial} → (bToC : Arrow B C) → idArrow ∘ₚ bToC ≡ bToC
composeLeftIdentity (_ ⇆ _) = refl

composeRightIdentity :{B C : Polynomial} → (cToB : Arrow C B) → cToB ∘ₚ idArrow ≡ cToB
composeRightIdentity (_ ⇆ _) = refl

composeIsAssoc : ∀ {A B C D} → {f : Arrow A B} {g : Arrow B C} {h : Arrow C D} → ((h ∘ₚ g) ∘ₚ f) ≡ (h ∘ₚ (g ∘ₚ f))
composeIsAssoc = refl
---------------------------------------

equiv-resp : {A B C : Polynomial} {f h : Arrow B C} {g i : Arrow A B} → f ≡ h → g ≡ i → (f ∘ₚ g) ≡ (h ∘ₚ i)
equiv-resp  p q ii = (p ii) ∘ₚ (q ii)

fromFalseFunctionsEqual : {A : Type} (f : ⊥ → A) → (g : ⊥ → A) → f ≡ g
fromFalseFunctionsEqual f g = funExt λ {()}


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
        toRight (mapPosition ⇆ mapDirection) pos = mapDirection pos tt

        toLeft : {p : Polynomial} → ((i : Polynomial.position p) → Polynomial.direction p i) → enclose p
        toLeft p₁ = (λ x → tt) ⇆ λ fromPos x → p₁ fromPos

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

 

isConstant : Polynomial → Type₁
isConstant (MkPoly pos dir) = (p : pos) → dir p ≡ ⊥

-- Exercise 4.1
constantClosedUnderPlus : {p q : Polynomial} → isConstant p → isConstant q → isConstant (p + q)
constantClosedUnderPlus isConstantP isConstantQ (inj₁ x) = isConstantP x
constantClosedUnderPlus isConstantP isConstantQ (inj₂ y) = isConstantQ y

constantClosedUnderMult : {p q : Polynomial} → isConstant p → isConstant q → isConstant (p * q)
constantClosedUnderMult isConstantP isConstantQ (posP , posQ) = lemma (isConstantP posP) (isConstantQ posQ)
  where
    lemma2 : {A B : Set} → A ≡ ⊥ → B ≡ ⊥ → (A ⊎ B) ≡ (⊥ ⊎ ⊥)
    lemma2 p₁ p₂ = {! cong ? p₁   !}

    lemma : {A B : Set} → A ≡ ⊥ → B ≡ ⊥ → (A ⊎ B) ≡ ⊥
    lemma {A = A} {B = B} p₁ p₂ = lemma2 p₁ p₂ ∙ {!  !}

isLinear : Polynomial → Type₁
isLinear (MkPoly pos dir) = (p : pos) → dir p ≡ ⊤

linearClosedUnderPlus : {p q : Polynomial} → isLinear p → isLinear q → isLinear (p + q)
linearClosedUnderPlus isLinearP isLinearQ (inj₁ x) = isLinearP x
linearClosedUnderPlus isLinearP isLinearQ (inj₂ y) = isLinearQ y

-- yoyo : {p q r : Polynomial} → (p + q) ◂ r ≡ (p ◂ r) + (q ◂ r)
-- yoyo {p} {q} {r} = poly≡∀ pos≡ λ {(inj₁ x) → {! cong (λ y → Σ (direction p (proj₁ x)) y) ?   !}
--                                 ; (inj₂ y) → {!   !}}
--   where
--     pos≡ : Σ (position p ⊎ position q)
--         (λ i → [ direction p , direction q ] i → position r)
--         ≡
--         (Σ (position p) (λ i → direction p i → position r) ⊎
--         Σ (position q) (λ i → direction q i → position r))
--     pos≡ = isoToPath (iso (λ {(inj₁ x , snd₁) → inj₁ (x , snd₁)
--                             ; (inj₂ y , snd₁) → inj₂ (y , snd₁)}) (λ {(inj₁ (fst₁ , snd₁)) → inj₁ fst₁ , snd₁
--                                                                     ; (inj₂ y) → inj₂ (proj₁ y) , snd y}) (λ {(inj₁ x) → refl
--                                                                                                             ; (inj₂ y) → refl}) λ {(inj₁ x , snd₁) → refl
--                                                                                                                                  ; (inj₂ y , snd₁) → refl})
    -- dir≡ : subst (λ x → x → Type) pos≡
    --   (direction (p + q) ◂ r)
    --   ≡ [ direction (p ◂ r) , direction (q ◂ r) ]
    -- dir≡ = ?

arrowToYIsChoiceOfDirection : {p : Polynomial} → Arrow p Y ≡ ((pos : position p) → direction p pos)
arrowToYIsChoiceOfDirection {p} = isoToPath (iso (λ { (_ ⇆ md) pos → md pos tt} )
                                                 (λ { mapSelfDir → const tt ⇆ λ fromPos _ → mapSelfDir fromPos}) 
                                                 (λ b → refl) 
                                                 (λ { (mp ⇆ md) → λ _ → const tt ⇆ md }) )   

