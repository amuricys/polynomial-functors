{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Proofs where

open import CategoryData.Everything
open import Level
open import Agda.Builtin.Unit
open import Data.Empty
import Relation.Binary.PropositionalEquality as Eq
open import Cubical.Data.Equality using (eqToPath ; pathToEq)
open import Cubical.Core.Everything
open import Cubical.Categories.Category
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Categories.Limits.Terminal
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties
open import Data.Product hiding (Σ-syntax)
open import Cubical.LensEquality
open import Data.Sum
open import Cubical.PolynomialEquals
open import Function

------- Categorical axioms
---------------------------------------
composeLeftIdentity : {B C : Polynomial} → (bToC : Lens B C) → idLens ∘ₚ bToC ≡ bToC
composeLeftIdentity (_ ⇆ _) = refl

composeRightIdentity :{B C : Polynomial} → (cToB : Lens C B) → cToB ∘ₚ idLens ≡ cToB
composeRightIdentity (_ ⇆ _) = refl

composeIsAssoc : ∀ {A B C D} → {f : Lens A B} {g : Lens B C} {h : Lens C D} → ((h ∘ₚ g) ∘ₚ f) ≡ (h ∘ₚ (g ∘ₚ f))
composeIsAssoc = refl
---------------------------------------

∘-resp-≈ : {A B C : Polynomial} {f h : Lens B C} {g i : Lens A B} → f ≡ h → g ≡ i → (f ∘ₚ g) ≡ (h ∘ₚ i)
∘-resp-≈  p q ii = (p ii) ∘ₚ (q ii)

fromFalseFunctionsEqual : {A : Type} (f : ⊥ → A) → (g : ⊥ → A) → f ≡ g
fromFalseFunctionsEqual f g = funExt λ {()}
 

------- Proofs related to uniqueness of lenses from and to certain polynomials
---------------------------------------
lensFromZeroUnique : {p : Polynomial} (f : Lens 𝟘 p) → lensFromZero ≡ f
lensFromZeroUnique f = lensesEqual3 (funExt λ ()) λ ()

lensToOneUnique : {p : Polynomial} (f : Lens p 𝟙) →  lensToOne ≡ f
lensToOneUnique {p = p} f = lensesEqual3 refl λ _ ()

---------------------------------------

------- Proofs related to plugging in 0
---------------------------------------
fromMapInDirectionToFunction : {p q : Polynomial} → (Polynomial.position p → Polynomial.position q) → p ⦅ ⊤ ⦆ → q ⦅ ⊤ ⦆
fromMapInDirectionToFunction {p} {q} f = \x →
  f (fst x) , λ _ → tt

fromFunctionToMapOnPositions : {p q : Polynomial} → (p ⦅ ⊤ ⦆ → q ⦅ ⊤ ⦆) → (Polynomial.position p → Polynomial.position q)
fromFunctionToMapOnPositions {p@(mkpoly pos dir)} {q} f = \x → let
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


------- Specific lens equalities
---------------------------------------
pwiseToExt : {A B : Set} {f g : A → B} → ({x : A} → f x Eq.≡ g x) → f ≡ g
pwiseToExt {A = A} {f = f} {g = g} p = let
  yaaa : {x : A} → f x ≡ g x
  yaaa = eqToPath p
  in
  funExt (λ x → yaaa)

positionLensesEqual : {A B : Polynomial} → {f g : Lens A B} → f ≡ g → Lens.mapPosition f ≡ Lens.mapPosition g
positionLensesEqual p i = Lens.mapPosition (p i)

positionLensesEqualPwise : {A B : Polynomial} →  {f g : Lens A B} {z : Polynomial.position A} → f ≡ g → Lens.mapPosition f z ≡ Lens.mapPosition g z
positionLensesEqualPwise {z = z} p i = let
  posEq = positionLensesEqual p i
  in posEq z

positionLensesEqualPwiseEq : {A B : Polynomial} {f g : Lens A B} →
      f ≡ g →
      {x : Polynomial.position A} →
      Lens.mapPosition f x Eq.≡ Lens.mapPosition g x
positionLensesEqualPwiseEq p = pathToEq (positionLensesEqualPwise p)
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
-- derivative (mkpoly pos dir) = mkpoly (Σ pos dir) (λ {(i , a) → {! dir i - a  !}})

import Relation.Binary.PropositionalEquality as Eq


isConstant : Polynomial → Type₁
isConstant (mkpoly pos dir) = (p : pos) → dir p ≡ ⊥


-- Exercise 4.1
constantClosedUnderPlus : {p q : Polynomial} → isConstant p → isConstant q → isConstant (p + q)
constantClosedUnderPlus isConstantP isConstantQ (inj₁ x) = isConstantP x
constantClosedUnderPlus isConstantP isConstantQ (inj₂ y) = isConstantQ y

constantClosedUnderMult : {p q : Polynomial} → isConstant p → isConstant q → isConstant (p * q)
constantClosedUnderMult isConstantP isConstantQ (posP , posQ) = lemma (isConstantP posP) (isConstantQ posQ)
  where
    lemma2 : {A B : Set} → A Eq.≡ ⊥ → B Eq.≡ ⊥ → (A ⊎ B) ≡ (⊥ ⊎ ⊥)
    lemma2 Eq.refl Eq.refl = refl

    lemma : {A B : Set} → A ≡ ⊥ → B ≡ ⊥ → (A ⊎ B) ≡ ⊥
    lemma {A = A} {B = B} p₁ p₂ = lemma2 (pathToEq p₁) (pathToEq p₂) ∙ isoToPath (iso (λ { (inj₁ ()) ; (inj₂ ()) }) (λ ()) (λ () ) (λ { (inj₁ ()) ; (inj₂ ()) }))

isLinear : Polynomial → Type₁
isLinear (mkpoly pos dir) = (p : pos) → dir p ≡ ⊤

linearClosedUnderPlus : {p q : Polynomial} → isLinear p → isLinear q → isLinear (p + q)
linearClosedUnderPlus isLinearP isLinearQ (inj₁ x) = isLinearP x
linearClosedUnderPlus isLinearP isLinearQ (inj₂ y) = isLinearQ y

isMonomial : Polynomial → Type₁
isMonomial (mkpoly pos dir) = ∀ {p₁ : pos} {p₂ : pos} → dir p₁ ≡ dir p₂

isMonomialΣ : Polynomial → Type₁
isMonomialΣ (mkpoly pos dir) = Σ[ A ∈ Set ] ({p : pos} → dir p ≡ A)   -- ∀ {p₁ : pos} {p₂ : pos} → dir p₁ ≡ dir p₂

-- equalProofs : {p : Polynomial} → isMonomial p ≡ isMonomialΣ p
-- equalProofs {mkpoly pos dir} = {!   !} -- isoToPath (iso (λ x → _ , λ {po} → {!   !}) {!   !} {!   !} {!   !})

monomialClosedUnderMult : {p q : Polynomial} → isMonomial p → isMonomial q → isMonomial (p * q)
monomialClosedUnderMult isMonP isMonQ {posp₁ , posq₁} {posp₂ , posq₂} = cong (λ { (a , b) → a ⊎ b }) (ΣPathP (leftEqual , rightEqual))
  where leftEqual = isMonP {posp₁} {posp₂}
        rightEqual = isMonQ {posq₁} {posq₂}

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

lensToYIsChoiceOfDirection : {p : Polynomial} → Lens p Y ≡ ((pos : position p) → direction p pos)
lensToYIsChoiceOfDirection {p} = isoToPath (iso (λ { (_ ⇆ md) pos → md pos tt} )
                                                 (λ { mapSelfDir → const tt ⇆ λ fromPos _ → mapSelfDir fromPos}) 
                                                 (λ b → refl) 
                                                 (λ { (mp ⇆ md) → λ _ → const tt ⇆ md }) )   

open import Data.Fin renaming (zero to z ; suc to s)
open import Data.Bool

ex⦅2⦆≡4 : ex ⦅ Bool ⦆ ≡ Fin 6
ex⦅2⦆≡4 = isoToPath $
  iso go 
      back
      sec
      ret
    where go : ex ⦅ Bool ⦆ → Fin 6
          go (false , fromboo) with fromboo false | fromboo true
          ... | false | false = z
          ... | true  | false = s z
          ... | false | true  = s (s z)
          ... | true  | true  = s (s (s z))
          go (true , fromboo) with fromboo tt
          ... | false         = s (s (s (s z)))
          ... | true          = s (s (s (s (s z))))
          back : Fin 6 → ex ⦅ Bool ⦆
          back z                     = false , λ { false → false ; true → false }
          back (s z)                 = false , λ { false → true ; true → false }
          back (s (s z))             = false , λ { false → false ; true → true }
          back (s (s (s z)))         = false , λ { false → true ; true → true }
          back (s (s (s (s z))))     = true ,  λ { tt → false }
          back (s (s (s (s (s z))))) = true ,  λ { tt → true }
          sec : section go back
          sec z                     = refl
          sec (s z)                 = refl
          sec (s (s z))             = refl
          sec (s (s (s z)))         = refl
          sec (s (s (s (s z))))     = refl
          sec (s (s (s (s (s z))))) = refl
          ret : retract go back
          ret (false , fromboo) with fromboo false in eq | fromboo true in eq2
          ... | false | false = ΣPathP (refl , funExt (λ { false → eqToPath (Eq.sym eq) ; true → eqToPath (Eq.sym eq2)} ))
          ... | true  | false = ΣPathP (refl , funExt (λ { false → eqToPath (Eq.sym eq) ; true → eqToPath (Eq.sym eq2)} ))
          ... | false | true  = ΣPathP (refl , funExt (λ { false → eqToPath (Eq.sym eq) ; true → eqToPath (Eq.sym eq2)} ))
          ... | true  | true  = ΣPathP (refl , funExt (λ { false → eqToPath (Eq.sym eq) ; true → eqToPath (Eq.sym eq2)} ))
          ret (true , fromboo) with fromboo tt in eq
          ... | false         = ΣPathP (refl , funExt (λ { tt → eqToPath (Eq.sym eq) } ))
          ... | true          = ΣPathP (refl , funExt (λ { tt → eqToPath (Eq.sym eq) } ))