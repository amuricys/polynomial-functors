{-# OPTIONS --cubical #-}

module Categorical.CartesianClosed where

open import Common.CategoryData
open import Categorical.CubicalPoly

import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (Σ-syntax ; curry ; uncurry)
open import Categorical.Product
open import Categories.Object.Product Poly
open import Categorical.Terminal
open import Cubical.Proofs
open import Cubical.ArrowEquals
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
import Categories.Category.CartesianClosed.Canonical Poly as Canonical

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = MkPolynomial ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))
eval : {p q : Polynomial} -> Arrow ((q ^ p) * p) q
eval {p} {q} = mapPos ⇄ mapDir
    where
        mapPos : position ((q ^ p) * p) → position q
        mapPos (posQ^P , posP) = fst (posQ^P posP)

        mapDir : (pos : position ((q ^ p) * p))
            → direction q (mapPos pos) 
            → direction ((q ^ p) * p) pos
        mapDir (posQ^P , posP) dir with (snd (posQ^P posP)) dir in eq
        ... | inj₂ y = inj₂ y
        ... | inj₁ x = inj₁ (posP , dir , help)
            where
                help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posQ^P posP) dir)
                help rewrite eq = tt

curry : {p q r : Polynomial} → Arrow (p * q) r → Arrow p (r ^ q)
curry {p} {q} {r} (f ⇄ f♯) = mapPos ⇄ mapDir
    where
        eraseLeft : {A B : Set} → A ⊎ B → ⊤ ⊎ B
        eraseLeft f = [ (λ _ → inj₁ tt) , inj₂ ] f

        mapPos : position p → position (r ^ q)
        mapPos posP posQ = f (posP , posQ) , λ {dirR → eraseLeft  (f♯ (posP , posQ) dirR)}

        mapDir : (pos : position p) → direction (r ^ q) (mapPos pos) → direction p pos
        mapDir posP (posQ , dirR , g) with f♯ (posP , posQ) dirR
        ... | inj₁ x = x

uncurry : {p q r : Polynomial} → Arrow p (q ^ r) → Arrow (p * r) q
uncurry {p} {q} {r} (f ⇄ f♯) = mapPos ⇄ mapDir
    where
        mapPos : position (p * r) → position q
        mapPos (posP , posR) = fst (f posP posR)

        mapDir : (pos : position (p * r)) → direction q (mapPos pos) → direction (p * r) pos
        mapDir (posP , posR) dirQ with snd (f posP posR) dirQ in eq
        ... | inj₂ y = inj₂ y
        ... | inj₁ x = inj₁ (f♯ posP (posR , dirQ , help))
            where
                help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (f posP posR) dirQ)
                help rewrite eq = tt

-- uncurryCurry : {p q r : Polynomial} (f : Arrow (p * q) r) → uncurry (curry f) ≡ f
-- uncurryCurry {p} {q} {r} f@(mapPos ⇄ mapDir) = arrow≡ refl (substRefl {B = λ (mapPos : position (p * q) → position r) → (fromPos : position (p * q)) → direction r (mapPos fromPos) → direction (p * q) fromPos } (Arrow.mapDirection (uncurry (curry (mapPos ⇄ mapDir))))) ∙ {!!}

-- arrow≡ refl (substRefl {B = (λ (mapPos : (position (p * q)) → (position r))  →
--          (fromPos : position (p * q)) →
--          direction r (mapPos fromPos) → direction (p * q) fromPos)} {x = Arrow.mapPosition f} (Arrow.mapDirection (uncurry (curry f))) ∙ lemma) -- (substRefl {B = (λ mapPos → (fromPos : position (p * q)) → direction r (mapPos fromPos) → direction (p * q) fromPos)} (Arrow.mapDirection (uncurry (curry f))) ∙ lemma) -- (substRefl {B = {!   !}} (Arrow.mapDirection (uncurry (curry f))) ∙ lemma) 
    -- where 
    --     lemma : Arrow.mapDirection (uncurry (curry (mapPos ⇄ mapDir))) ≡ Arrow.mapDirection (mapPos ⇄ mapDir)
    --     lemma = funExt (λ {(posQ , posP) → {!   !}})


-- curryUncurry : {p q r : Polynomial} {f : Arrow p (q ^ r) } → curry (uncurry f) ≡ f
-- curryUncurry {f = f} = arrow≡ (funExt λ posP → funExt λ posR → {!   !}) {!   !} -- arrowsEqual3 posEq λ { x (fst₁ , snd₁) → {!   !}}
--     where
--         posEq : Arrow.mapPosition (curry (uncurry f)) ≡ Arrow.mapPosition f
--         -- posEq = funExt λ posA → funExt λ posB → ΣPathTransport→PathΣ (Arrow.mapPosition (curry (uncurry f)) posA posB) (Arrow.mapPosition f posA posB) (refl , {!   !})
--         posEq = funExt λ posA → funExt λ posB → {!  Σ-cong' ? !}


r^q : (r : Polynomial) -> (q : Polynomial) -> Polynomial
r^q r (MkPolynomial posQ dirQ) = depProd (posQ , λ j → r ◂ (Y + Constant (dirQ j)))

mpEv : {A B : Polynomial} → position (r^q B A * A) → position B
mpEv (posB^A , posA) = fst (posB^A posA)
mdEv : {A B : Polynomial} → (fromPos : position (r^q B A * A)) → direction B (mpEv fromPos) → direction (r^q B A * A) fromPos
mdEv (posB^A , posA) x with (snd (posB^A posA)) x in eq
... | inj₂ v = inj₂ v
... | inj₁ s = inj₁ (posA , x , help eq)
        where help : (snd (posB^A posA) x) Eq.≡ inj₁ s -> [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posB^A posA) x)
              help p rewrite p = tt
ev : {A B : Polynomial} -> Arrow (r^q B A * A) B
ev {A} {B} = mpEv ⇄ mdEv

-- lemma : {C A B : Polynomial} {f@(mp ⇄ md) : Arrow (C * A) B} {posC : position C} {posA : position A} → (direction B (mp (posC , posA)) → direction (C * A) (posC , posA) ) → direction B (mp (posC , posA)) → position (Y + Constant (direction A posA))
-- lemma f x with f x
-- ... | inj₁ x₁ = inj₁ tt
-- ... | inj₂ y = inj₂ y
-- mpCurry : {C A B : Polynomial} {f : Arrow (C * A) B} → position C → position (r^q B A)
-- mpCurry {C} {A} {B} {f = f@(mp ⇄ md)} posC posA = mp (posC , posA) , lemma {C} {A} {B} {f} {posC} {posA} (md (posC , posA))
-- mdCurry : {C A B : Polynomial} {f : Arrow (C * A) B} (fromPos : position C) → direction (r^q B A) (mpCurry {C} {A} {B} {f} fromPos) → direction C fromPos
-- mdCurry {C} {A} {B} {f = (mp ⇄ md)} posC (posA , fst , snd) with res <- (md (posC , posA) fst) in eq with res with snd 
-- ... | inj₁ x | tt = x
-- ... | inj₂ y | ()
-- curry : {C A B : Polynomial} → Arrow (C * A) B → Arrow C (r^q B A)
-- curry {C} {A} {B} f = mpCurry {C} {A} {B} {f} ⇄ mdCurry {C} {A} {B} {f}



canonical : {A B : Polynomial} -> Canonical.CartesianClosed
canonical {A} {B} = record
    { ⊤ = One
    ; _×_ = _*_
    ; ! = arrowToOne
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; !-unique = arrowToOneUnique
    ; π₁-comp = refl
    ; π₂-comp = refl
    ; ⟨,⟩-unique = unique
    ; _^_ = _^_
    ; eval = eval
    ; curry = curry
    ; eval-comp =  {!   !}
    ; curry-resp-≈ = cong curry
    ; curry-unique = {!   !}
    }
    --   where

    --     -- helper : {p A B : Polynomial} {h : Arrow p (A * B)} -> ⟨ π₁ ∘p h , π₂ ∘p h ⟩ ≡ h
    --     -- helper {h = h} = arrowsEqual2 refl λ { x (inj₁ x1) → cong (λ zz → Arrow.mapDirection h x (inj₁ zz)) (sym (transportRefl  x1))
    --     --                                     ;  x (inj₂ y) → cong (λ zz → Arrow.mapDirection h x (inj₂ zz))  (sym (transportRefl y)) } -- λ i fromPos x → {!   !} -- (transportRefl {!   !} {!   !})

    --     -- unique : {F A B : Polynomial} {h : Arrow F (A * B)} {f₁ : Arrow F A} {f₂ : Arrow F B} →
    --     --     (π₁ ∘p h) ≡ f₁ →
    --     --     (π₂ ∘p h) ≡ f₂ → 
    --     --     ⟨ f₁ , f₂ ⟩ ≡ h
    --     -- unique {F = F} {h = h} p₁ p₂ = transitivity (λ i → ⟨ sym p₁ i , sym p₂ i ⟩) (helper {p = F} {h = h})

    --     unique : {F A B : Polynomial} {h : Arrow F (A * B)} {f₁ : Arrow F A} {f₂ : Arrow F B} →
    --         (π₁ ∘p h) ≡ f₁ →
    --         (π₂ ∘p h) ≡ f₂ → 
    --         ⟨ f₁ , f₂ ⟩ ≡ h
    --     unique {F = F} {h = h} p₁ p₂ = transitivity (λ i → ⟨ sym p₁ i , sym p₂ i ⟩) (helper {p = F} {h = h})
                
    --     _×a_ : {A B C D : Polynomial} → (f : Arrow A C) (g : Arrow B D) → Arrow (A * B) (C * D)
    --     (mpf ⇄ mdf) ×a (mpg ⇄ mdg) = (λ {(a , b) → mpf a , mpg b}) ⇄ λ {(a , b) (inj₁ x) → inj₁ (mdf a x) 
    --                                                                   ; (a , b) (inj₂ y) → inj₂ (mdg b y) }
    --     eval-comp-simple : {A B C D E : Polynomial} → 
    --                 (f : Arrow (E * D) C) → 
    --                 (ev ∘p (curry f ×a idArrow))
    --                 ≡ f
    --     eval-comp-simple {A} {B} {C} {D} {E} f = arrowsEqual3 refl helper2
    --         where
    --             helper2 : (x@(e , d) : position (E * D)) 
    --                     → (y : direction C (Arrow.mapPosition f x))
    --                     → Arrow.mapDirection (ev ∘p (curry f ×a idArrow)) x (subst (λ mapPos → direction C (mapPos x)) (sym (λ _ → Arrow.mapPosition (ev ∘p (curry f ×a idArrow)))) y) ≡ Arrow.mapDirection f x y
    --             helper2 x@(e , d) y with Arrow.mapDirection f x y
    --             ... | inj₁ x₁ = {!   !} -- cong {!  !} {!  !}
    --             ... | inj₂ y₁ = subst (λ eqv → eqv ≡ inj₂ y₁) proof2 refl
    --                  where 
    --                        proof2 : inj₂ y₁ ≡
    --                                 (λ { (a , b) (inj₁ x) → inj₁ (mdCurry a x)
    --                                    ; (a , b) (inj₂ y) → inj₂ y
    --                                    })
    --                                 (e , d)
    --                                 (mdEv
    --                                 ((λ posA →
    --                                     Arrow.mapPosition f (e , posA) ,
    --                                     (λ x₁ →
    --                                         lemma (Arrow.mapDirection f (e , posA)) x₁
    --                                         | Arrow.mapDirection f (e , posA) x₁))
    --                                     , d)
    --                                 (transp (λ i → direction C (Arrow.mapPosition f (e , d))) i0 y)
    --                                 | (lemma (Arrow.mapDirection f (e , d))
    --                                     (transp (λ i → direction C (Arrow.mapPosition f (e , d))) i0 y)
    --                                     | Arrow.mapDirection f (e , d)
    --                                         (transp (λ i → direction C (Arrow.mapPosition f (e , d))) i0 y))
    --                                 | Eq.refl)
    --                        proof2 = {!   !}

                                    

  
