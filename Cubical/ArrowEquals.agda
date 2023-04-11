{-# OPTIONS --cubical #-}

module Cubical.ArrowEquals where

open import CategoryData.Core
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties

open Polynomial
open Arrow

ArrowAsSigma : Polynomial → Polynomial → Type
ArrowAsSigma p q = Σ[ mapPos ∈ (position p → position q) ]
    ((fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos)
    
sigmaToArrow : {p q : Polynomial} → ArrowAsSigma p q → Arrow p q
sigmaToArrow (mapPos , mapDir) = mapPos ⇄ mapDir

arrowToSigma : {p q : Polynomial} → Arrow p q → ArrowAsSigma p q
arrowToSigma  (mapPos ⇄ mapDir) = mapPos , mapDir

arrow≡arrowSigma : {p q : Polynomial} → (Arrow p q) ≡ (ArrowAsSigma p q)
arrow≡arrowSigma = isoToPath (iso arrowToSigma sigmaToArrow (λ b → refl) (λ a → refl))

arrowSigmas≡ : {p q : Polynomial} (f g : ArrowAsSigma p q)
    → (fstF≡fstG : fst f ≡ fst g)
    -- Goal: (fromPos : Polynomial.position p) → Polynomial.direction q (fst g fromPos) → Polynomial.direction p fromPos
    -- Have: (fromPos : Polynomial.position p) → Polynomial.direction q (fst f fromPos) → Polynomial.direction p fromPos
    -- subst to match.
    → subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) fstF≡fstG (snd f) ≡ snd g
    → f ≡ g
arrowSigmas≡ f g fstF≡fstG sndF≡sndG = ΣPathTransport→PathΣ f g (fstF≡fstG , sndF≡sndG)

-- Same as arrowSigmas≡ but do subst on other side
arrowSigmas≡' : {p q : Polynomial} (f g : ArrowAsSigma p q) 
    → (fstF≡fstG : fst f ≡ fst g)
    -- Goal: (fromPos : Polynomial.position p) → Polynomial.direction q (fst f fromPos) → Polynomial.direction p fromPos
    -- Have: (fromPos : Polynomial.position p) → Polynomial.direction q (fst g fromPos) → Polynomial.direction p fromPos
    → snd f ≡ (subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) (sym fstF≡fstG) (snd g))
    → f ≡ g
arrowSigmas≡' f g fstF≡fstG sndF≡sndG = sym (ΣPathTransport→PathΣ g f (sym fstF≡fstG , sym sndF≡sndG))


arrow≡ : {p q : Polynomial} {f g : Arrow p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g) 
    → subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) mapPos≡ (mapDirection f) ≡ mapDirection g
    → f ≡ g
arrow≡ {p} {q} {f} {g} mapPos≡ mapDir≡ i = sigmaToArrow ((arrowSigmas≡ {q = q} (arrowToSigma f) (arrowToSigma g) mapPos≡ mapDir≡ i))

arrow≡' : {p q : Polynomial} {f g : Arrow p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g) 
    → mapDirection f ≡ (subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) (sym mapPos≡) (mapDirection g))
    → f ≡ g
arrow≡' {p} {q} {f} {g} mapPos≡ mapDir≡ i = sigmaToArrow ((arrowSigmas≡' {q = q} (arrowToSigma f) (arrowToSigma g) mapPos≡ mapDir≡ i))

arrow≡∀ : {p q : Polynomial} {f g : Arrow p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g)
    → ((fromPos : position p) → subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) mapPos≡ (mapDirection f) fromPos ≡ mapDirection g fromPos)
    → f ≡ g
arrow≡∀ mapPos≡ mapDir≡ = arrow≡ mapPos≡ λ i fromPos → mapDir≡ fromPos i

arrow≡∀' : {p q : Polynomial} {f g : Arrow p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g)
    → ( (fromPos : position p) → mapDirection f fromPos ≡ (subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) (sym mapPos≡) (mapDirection g)) fromPos)
    → f ≡ g
arrow≡∀' mapPos≡ mapDir≡ = arrow≡' mapPos≡ λ i fromPos → mapDir≡ fromPos i

arrow≡∀∀ : {p q : Polynomial} {f g : Arrow p q}
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
arrow≡∀∀ mapPos≡ mapDir≡ = arrow≡ mapPos≡ λ i fromPos x → mapDir≡ fromPos x i

arrow≡∀∀' : {p q : Polynomial} {f g : Arrow p q}
    → (mapPos≡ : mapPosition f ≡ mapPosition g)
    → ((fromPos : position p) → (dirQFromF : direction q (mapPosition f fromPos)) → mapDirection f fromPos dirQFromF ≡ (subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) (sym mapPos≡) (mapDirection g)) fromPos dirQFromF)
    → f ≡ g
arrow≡∀∀' mapPos≡ mapDir≡ = arrow≡' mapPos≡ λ i fromPos x → mapDir≡ fromPos x i

-- arrow≡∀∀
-- have: → ((fromPos : position p) → (dirQFromG : direction q (mapPosition g fromPos)) → subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) mapPos≡ (mapDirection f) fromPos dirQFromG ≡ mapDirection g fromPos dirQFromG)
-- arrowEquals3
-- want: → ((fromPos : position p) → (dirQFromG : direction q (mapPosition g fromPos)) → mapDirection f fromPos  (subst (λ mapPos → direction q (mapPos fromPos)) (sym mapPosEq) dirQFromG)                                       ≡ mapDirection g fromPos dirQFromG)

-- middle part that differ
-- have: subst (λ mapPos → (fromPos : position p) → direction q (mapPos fromPos) → direction p fromPos) mapPos≡ (mapDirection f) fromPos dirQFromG
-- want: mapDirection f fromPos  (subst (λ mapPos → direction q (mapPos fromPos)) (sym mapPosEq) dirQFromG)
