{-# OPTIONS --cubical #-}

module Cubical.LensEquality where

open import CategoryData.Core
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties
open import Cubical.Functions.FunExtEquiv
open import Cubical.Foundations.Path
open import Cubical.Foundations.Transport


open Polynomial
open Lens

LensAsSigma : Polynomial → Polynomial → Type
LensAsSigma p q = Σ[ mapPos ∈ (position p → position q) ]
    ((fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos)
    
sigmaToLens : {p q : Polynomial} → LensAsSigma p q → Lens p q
sigmaToLens (mapPos , mapDir) = mapPos ⇆ mapDir

lensToSigma : {p q : Polynomial} → Lens p q → LensAsSigma p q
lensToSigma  (mapPos ⇆ mapDir) = mapPos , mapDir

lens≡lensSigma : {p q : Polynomial} → (Lens p q) ≡ (LensAsSigma p q)
lens≡lensSigma = isoToPath (iso lensToSigma sigmaToLens (λ b → refl) (λ a → refl))

lensSigmas≡ : {p q : Polynomial} (f g : LensAsSigma p q)
    → (fstF≡fstG : fst f ≡ fst g)
    -- Goal: (fromPos : Polynomial.position p) → Polynomial.direction q (fst g fromPos) → Polynomial.direction p fromPos
    -- Have: (fromPos : Polynomial.position p) → Polynomial.direction q (fst f fromPos) → Polynomial.direction p fromPos
    -- subst to match.
    → subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) fstF≡fstG (snd f) ≡ snd g
    → f ≡ g
lensSigmas≡ f g fstF≡fstG sndF≡sndG = ΣPathTransport→PathΣ f g (fstF≡fstG , sndF≡sndG)

-- Same as lensSigmas≡ but do subst on other side
lensSigmas≡' : {p q : Polynomial} (f g : LensAsSigma p q) 
    → (fstF≡fstG : fst f ≡ fst g)
    -- Goal: (fromPos : Polynomial.position p) → Polynomial.direction q (fst f fromPos) → Polynomial.direction p fromPos
    -- Have: (fromPos : Polynomial.position p) → Polynomial.direction q (fst g fromPos) → Polynomial.direction p fromPos
    → snd f ≡ (subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) (sym fstF≡fstG) (snd g))
    → f ≡ g
lensSigmas≡' f g fstF≡fstG sndF≡sndG = sym (ΣPathTransport→PathΣ g f (sym fstF≡fstG , sym sndF≡sndG))



lens≡ : {p q : Polynomial} {f g : Lens p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g) 
    → subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) mapPos≡ (mapDirection f) ≡ mapDirection g
    → f ≡ g
lens≡ {p} {q} {f} {g} mapPos≡ mapDir≡ i = sigmaToLens ((lensSigmas≡ {q = q} (lensToSigma f) (lensToSigma g) mapPos≡ mapDir≡ i))

-- 

lens≡' : {p q : Polynomial} {f g : Lens p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g) 
    → mapDirection f ≡ (subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) (sym mapPos≡) (mapDirection g))
    → f ≡ g
lens≡' {p} {q} {f} {g} mapPos≡ mapDir≡ i = sigmaToLens ((lensSigmas≡' {q = q} (lensToSigma f) (lensToSigma g) mapPos≡ mapDir≡ i))

lens≡∀ : {p q : Polynomial} {f g : Lens p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g)
    → ((fromPos : position p) → subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) mapPos≡ (mapDirection f) fromPos ≡ mapDirection g fromPos)
    → f ≡ g
lens≡∀ mapPos≡ mapDir≡ = lens≡ mapPos≡ (funExt (λ fromPos → mapDir≡ fromPos))

lens≡∀' : {p q : Polynomial} {f g : Lens p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g)
    → ( (fromPos : position p) → mapDirection f fromPos ≡ (subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) (sym mapPos≡) (mapDirection g)) fromPos)
    → f ≡ g
lens≡∀' mapPos≡ mapDir≡ = lens≡' mapPos≡ (funExt (λ fromPos → mapDir≡ fromPos))

lens≡∀∀ : {p q : Polynomial} {f g : Lens p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g)
    → ( (fromPos : position p) → (dirQFromG : direction q (mapPosition g fromPos)) → 
          subst 
             (λ h → (x : position p) → direction q (h x) → direction p x)
             mapPos≡ 
             (mapDirection f)
             fromPos dirQFromG 
             ≡
           mapDirection g fromPos dirQFromG)
    → f ≡ g
lens≡∀∀ mapPos≡ mapDir≡ = lens≡ mapPos≡ (funExt λ fromPos → funExt λ x → mapDir≡ fromPos x)

lens≡∀∀' : {p q : Polynomial} {f g : Lens p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g)
    → ((fromPos : position p) → (dirQFromF : direction q (mapPosition f fromPos)) → mapDirection f fromPos dirQFromF ≡ (subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) (sym mapPos≡) (mapDirection g)) fromPos dirQFromF)
    → f ≡ g
lens≡∀∀' mapPos≡ mapDir≡ = lens≡' mapPos≡ λ i fromPos x → mapDir≡ fromPos x i


lensSigmasEqual3 : {p q : Polynomial} {f g : Lens p q}
    → (mapPosEq : Lens.mapPosition f ≡ Lens.mapPosition g)
    → ((x : position p) → (y : direction q (mapPosition g x)) → mapDirection f x  (subst (λ mapPos → direction q (mapPos x)) (sym mapPosEq) y) ≡ mapDirection g x y)
    → lensToSigma f ≡ lensToSigma g
lensSigmasEqual3 {p = p} {q = q} {f = f} {g = g} mapPosEq mapDirEq = ΣPathP (mapPosEq , funExt λ x → funExtDep λ {y1} {y2} p → cong (mapDirection f x) (fromPathP⁻ p) ∙ mapDirEq x y2)

lensesEqual3 : {p q : Polynomial} {f g : Lens p q}
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
lensesEqual3 {f = f} {g = g} a b i = sigmaToLens (lensSigmasEqual3 {f = f} {g = g} a b i)

lens≡→mapPos≡ : {p q : Polynomial} {f g : Lens p q} → (f ≡ g) → (mapPosition f ≡ mapPosition g)
lens≡→mapPos≡ p = λ i → mapPosition (p i)

-- lens≡→mapDir≡ : {p q : Polynomial} {f g : Lens p q} → (f ≡ g) → (mapDirection f ≡ mapDirection g)
-- lens≡→mapDir≡ p = λ i → mapDirection (p i)