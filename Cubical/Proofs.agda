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
lensFromZeroUnique f = lens≡ₚ (funExt λ ()) λ ()

lensToOneUnique : {p : Polynomial} (f : Lens p 𝟙) →  lensToOne ≡ f
lensToOneUnique {p = p} f = lens≡ₚ refl λ _ ()

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

open import Data.Fin renaming (zero to z ; suc to s) using (Fin)
open import Data.Bool hiding (_∨_ ; _∧_)

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

       

data ThreeSet : Set where
  three1 three2 three3 : ThreeSet

data TwoSet : Set where
  two1 two2 : TwoSet

data NineSet : Set where
  nine1 nine2 nine3 nine4 nine5 nine6 nine7 nine8 nine9 : NineSet

Three : Polynomial
Three = mkpoly ThreeSet λ x → ⊥

Two : Polynomial
Two = mkpoly TwoSet (λ x → ⊥)

Nine : Polynomial
Nine = mkpoly NineSet (λ x → ⊥)

open import Cubical.Data.Equality using (pathToEq ; eqToPath) renaming (_≡_ to _≡p_)

3^2≡9 : Three ^ Two ≡ Nine
3^2≡9 = poly≡∀' pos≡ dir≡
  where other : ((index : TwoSet) → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)) ≡ NineSet
        other = isoToPath (iso go back proofSection proofRetract)
                where go : (TwoSet → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)) → NineSet
                      go two with ( two two1 , two two2 )
                      ... | (three1 , snd₁) , three1 , snd₂ = nine1
                      ... | (three1 , snd₁) , three2 , snd₂ = nine2
                      ... | (three1 , snd₁) , three3 , snd₂ = nine3
                      ... | (three2 , snd₁) , three1 , snd₂ = nine4
                      ... | (three2 , snd₁) , three2 , snd₂ = nine5
                      ... | (three2 , snd₁) , three3 , snd₂ = nine6
                      ... | (three3 , snd₁) , three1 , snd₂ = nine7
                      ... | (three3 , snd₁) , three2 , snd₂ = nine8
                      ... | (three3 , snd₁) , three3 , snd₂ = nine9
                      back : NineSet → TwoSet → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)
                      back nine1 two1 = three1 , λ ()
                      back nine1 two2 = three1 , (λ ())
                      back nine2 two1 = three1 , (λ ())
                      back nine2 two2 = three2 , (λ ())
                      back nine3 two1 = three1 , (λ ())
                      back nine3 two2 = three3 , (λ ())
                      back nine4 two1 = three2 , (λ ())
                      back nine4 two2 = three1 , (λ ())
                      back nine5 two1 = three2 , (λ ())
                      back nine5 two2 = three2 , (λ ())
                      back nine6 two1 = three2 , (λ ())
                      back nine6 two2 = three3 , (λ ())
                      back nine7 two1 = three3 , (λ ())
                      back nine7 two2 = three1 , (λ ())
                      back nine8 two1 = three3 , (λ ())
                      back nine8 two2 = three2 , (λ ())
                      back nine9 two1 = three3 , (λ ())
                      back nine9 two2 = three3 , (λ ())
                      proofSection : (b : NineSet) → go (back b) ≡ b
                      proofSection nine1 = refl
                      proofSection nine2 = refl
                      proofSection nine3 = refl
                      proofSection nine4 = refl
                      proofSection nine5 = refl
                      proofSection nine6 = refl
                      proofSection nine7 = refl
                      proofSection nine8 = refl
                      proofSection nine9 = refl
                      helper :  ∀ {X Y} {some : ⊥ → ⊤ ⊎ ⊥} → X ≡p (Y , some) → X ≡p (Y , (λ ()))
                      helper {X} {Y} one = pathToEq (eqToPath one ∙ cong (λ a → Y , a) functionFromFalse)
                        where functionFromFalse : {some : ⊥ → ⊤ ⊎ ⊥} → some ≡ λ ()
                              functionFromFalse = funExt (λ ())
                      proofRetract : (a : TwoSet → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)) → back (go a) ≡ a
                      proofRetract a with a two1 | a two2 | (Eq.inspect a two1) | (Eq.inspect a two2)
                      ... | (three1 , snd₁) | (three1 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
                      ... | (three1 , snd₁) | (three2 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
                      ... | (three1 , snd₁) | (three3 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
                      ... | (three2 , snd₁) | (three1 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
                      ... | (three2 , snd₁) | (three2 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
                      ... | (three2 , snd₁) | (three3 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
                      ... | (three3 , snd₁) | (three1 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
                      ... | (three3 , snd₁) | (three2 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
                      ... | (three3 , snd₁) | (three3 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ eqToPath ∘ helper $ eq₁; two2 → sym ∘ eqToPath ∘ helper $ eq₂}
        pos≡ : position (Three ^ Two) ≡ position Nine
        pos≡ = other
        dir≡ : (posA : (index : TwoSet) → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)) →
            Σ TwoSet
            (λ index →
              Σ ⊥ (λ a → [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posA index) a)))
            ≡ ⊥
        dir≡ p = isoToPath (iso (λ { () }) (λ ()) (λ ()) λ { () _ })
open import Cubical.Foundations.Path using ( toPathP⁻ )

open Iso
-- (iso (λ l x → fst (mapPosition l tt x))
--                                        (λ f → (λ _ index → (f index) , inj₂) ⇆ λ { fromPos () })
--                                        (λ b → refl)
--                                        λ a → {!   !})
linear^linear≡pos→pos : {A B : Set} → Lens 𝟙 (linear B ^ linear A) ≡ (A → B)
linear^linear≡pos→pos = isoToPath (iso (λ l x → fst (mapPosition l tt x))
                                       (λ f → (λ _ index → (f index) , inj₂) ⇆ λ { fromPos () })
                                       (λ b → refl)
                                       λ a → {!   !}) -- it's actually kind of hard to prove this

ΣAssoc : {A : Set} {B : A → Set} {C : (Σ A B) → Set} → (Σ (Σ A B) C) ≡ (Σ[ a ∈ A ] Σ[ b ∈ (B a) ] C (a , b)) 
ΣAssoc {A} {B} {C} = isoToPath (iso go back (λ b → refl) λ a → refl)
    where
        go : Σ (Σ A B) C → Σ A (λ a → Σ (B a) (λ b → C (a , b)))
        go ((a , b) , c) = a , b , c

        back : Σ A (λ a → Σ (B a) (λ b → C (a , b))) → Σ (Σ A B) C
        back (a , b , c) = (a , b) , c
linear^linear≡pos→pos {A} {B} = isoToPath is
  where is : Iso (Lens 𝟙 (linear B ^ linear A)) (A → B)
        fun is l x = fst (mapPosition l tt x)
        inv is f = (λ _ index → (f index) , inj₂) ⇆ λ { fromPos () }
        rightInv is b = refl
        leftInv is (mpa ⇆ mda) = lens≡ₚ {!   !} {!   !}
        -- it's actually kind of hard to prove this
ΣLemma : {A B : Set} {C : A → Set} {D : B → Set} → (pr₁ : A ≡ B) → (C ≡ λ a → D (transport pr₁ a)) → Σ A C ≡ Σ B D
ΣLemma pr₁ pr₂ = cong (λ {(A , B) → Σ A B}) (ΣPathP (pr₁ , (toPathP⁻ pr₂)))

leftDistribute◂ : {p q r : Polynomial} → (p + q) ◂ r ≡ (p ◂ r) + (q ◂ r)
leftDistribute◂ {p} {q} {r} = poly≡∀ pos≡ dir≡
  where pos≡ : position ((p + q) ◂ r) ≡ position (p ◂ r + q ◂ r)
        pos≡ = isoToPath (iso (λ { (inj₁ posp , dirpAtPosPtoR) → inj₁ (posp , dirpAtPosPtoR)
                                 ; (inj₂ posq , dirqAtPosQtoR) → inj₂ (posq , dirqAtPosQtoR) }) 
                              (λ { (inj₁ (posp , dirpAtPosPtoR)) → (inj₁ posp) , dirpAtPosPtoR
                                 ; (inj₂ (posq , dirqAtPosQtoR)) → (inj₂ posq) , dirqAtPosQtoR }) 
                              (λ { (inj₁ x) → refl
                                 ; (inj₂ y) → refl } ) 
                              λ { (inj₁ x , _) → refl 
                                ; (inj₂ y , _) → refl })
        dir≡ : (posB : position (p ◂ r) ⊎ position (q ◂ r)) → 
              subst (λ x → x → Type) pos≡ (dir (p + q) r) posB ≡ 
              [ direction (p ◂ r) , direction (q ◂ r) ] posB
        dir≡ (inj₁ x) = isoToPath (iso (λ { (dp , dr) → 
                                            subst (direction p) (transportRefl (proj₁ x)) dp , 
                                            subst (direction r) (transportRefl ((snd x (transp (λ j → direction p (transp (λ i → position p) j (proj₁ x))) i0 dp)))) dr })
                                       (λ { (dp , dr) → 
                                            subst (direction p) (sym (transportRefl (proj₁ x))) dp , 
                                            let sndtransp = (snd x
                                                            (transport (λ j → direction p (transp (λ i → position p) j (proj₁ x)))
                                                            (transport
                                                              (λ i → direction p (transp (λ _ → position p) (~ i) (proj₁ x)))
                                                              dp)))
                                                myeq : transport 
                                                       (λ j → direction p (transp (λ _ → position p) j (proj₁ x))) 
                                                       (transport 
                                                        (λ j → direction p (transp (λ _ → position p) (~ j) (proj₁ x))) dp)
                                                      ≡ dp
                                                myeq i = transp (λ j → direction p (transp (λ _ → position p) (i ∨ j) (proj₁ x))) i
                                                         (transp (λ j → direction p (transp (λ _ → position p) (i ∨ ~ j) (proj₁ x))) i dp)
                                                sndtranspiseq : snd x dp ≡ sndtransp
                                                sndtranspiseq = cong (snd x) (sym myeq)
                                                  -- λ i → 
                                                  -- transport (λ j → direction p (transp (λ _ → position p) {!  !} (proj₁ x)))
                                                  --           {!   !}
                                                k : direction r (snd x dp) ≡ direction r
                                                      (transport (λ i → position r)
                                                       (snd x
                                                        (transport (λ j → direction p (transp (λ i → position p) j (proj₁ x)))
                                                         (transport
                                                          (λ i → direction p (transp (λ _ → position p) (~ i) (proj₁ x)))
                                                          dp))))
                                                k = cong (direction r) (sndtranspiseq ∙ sym (transportRefl sndtransp)  )
                                            in transport k dr }) 
                                            (λ { (b₁ , b₂) → ΣPathP ((λ i → transp (λ i₃ → direction p (transp (λ _ → position p) (i₃ ∨ i) (proj₁ x)))
                                                                                      i 
                                                                                      (transp  (λ i₃ → direction p (transp (λ _ → position p) (i ∨ ~ i₃) (proj₁ x))) i b₁)) 
                                                                                      , 
                                                                      toPathP λ bigi → {!   !} ) }) 
                                            λ a → {!   !})
        dir≡ (inj₂ y) = {!   !}   
