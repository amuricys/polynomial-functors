{-# OPTIONS --cubical #-}
module Categorical.Exp where

open import CategoryData.Everything
open import Cubical.Foundations.Everything hiding () renaming (curry to curryₛ ; uncurry to uncurryₛ)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Equality using (pathToEq ; eqToPath)
open import Cubical.LensEquality
open import Cubical.Data.Sigma hiding (_×_)
open import Data.Unit
open import Data.Sum
open import Data.Empty
open import Cubical.Utils.CoproductUtils

eval : {p q : Polynomial} → Lens ((q ^ p) * p) q
eval {p} {q} = mapPos ⇆ mapDir
    where
        mapPos : position (q ^ p * p) → position q
        mapPos (posQ^P , posP) = fst (posQ^P posP)

        mapDir : (pos : position (q ^ p * p)) → direction q (mapPos pos) → direction (q ^ p * p) pos
        mapDir (posQ^P , posP) dir = recoverLeft (snd (posQ^P posP) dir) λ x → posP , dir , toImpossibleRight x

curry : {p q r : Polynomial} → Lens (r * p) q → Lens r (q ^ p)
curry {p} {q} {r} (g ⇆ g♯) = mapPos ⇆ mapDir
    where
        mapPos : position r → position (q ^ p)
        mapPos posR posP = g (posR , posP) , forgetLeft ∘ (g♯ (posR , posP))

        mapDir : (posR : position r) → direction (q ^ p) (mapPos posR) → direction r posR
        mapDir posR (posP , dir , pr) = keepLeft (g♯ (posR , posP) dir) (fromImpossibleRight pr)

uncurry : {p q r : Polynomial} → Lens r (q ^ p) → Lens (r * p) q
uncurry h = eval ∘ₚ ⟨ h × idLens ⟩

uncurry₂ : {p q r : Polynomial} → Lens r (q ^ p) → Lens (r * p) q
uncurry₂ {p} {q} {r} (h ⇆ h♯) = mapPos ⇆ mapDir
    where
        mapPos : position (r * p) → position q
        mapPos = fst ∘ uncurryₛ h

        mapDir : (pos : position (r * p)) → direction q (mapPos pos) → direction (r * p) pos
        mapDir (posR , posP) dir = recoverLeft (snd (h posR posP) dir) λ x → h♯ posR (posP , dir , toImpossibleRight x)

uncurrySame : {p q r : Polynomial} {h : Lens r (q ^ p)} → uncurry h ≡ uncurry₂ h
uncurrySame {p} {q} {r} h@{h' ⇆ h♯} = lensesEqual3 refl λ x y → {!   !}
    where
        dir≡ : (x : position (r * p)) (y : direction q (mapPosition (uncurry h) x)) → mapDirection (uncurry h) x y ≡ recoverLeft (snd (mapPosition h (fst x) (snd x)) y) (λ x₁ → mapDirection h (fst x) (snd x , y , toImpossibleRight x₁))
        dir≡ (posR , posP) dir = {!    !}

-- theorem : {p q : Polynomial} {f : Lens p q} → mapPosition ⟨ f × idLens ⟩ ≡ {! mapPosition f  !}
-- theorem = {!   !}

uncurryCurry : {p q r : Polynomial} {g : Lens (r * p) q} → uncurry₂ (curry g) ≡ g
uncurryCurry {p} {q} {r} {g} = lensesEqual3 refl λ x y → {!   !}
    where
        yo : (x : position (r * p)) (y : direction q (mapPosition (uncurry₂ (curry g)) x)) → mapDirection (uncurry₂ (curry g)) x y
            ≡ mapDirection g x y
        yo x y = subst (λ x₁ → recoverLeft (forgetLeft (mapDirection g x y)) (λ x₂ → keepLeft (mapDirection g x y) {! fromImpossibleRight ∘ toImpossibleRight  !}) ≡ recoverLeft (forgetLeft (mapDirection g x y)) (keepLeft (mapDirection g x y))) toFromImpossibleRight {!   !} ∙ recoverForgetLeft {x = mapDirection g x y} -- {!   !} ∙ {!   !} -- recoverForget {x = mapDirection g x y}


        -- recoverLeft (forgetLeft (mapDirection g (fst x , snd x) y))
        -- (λ x₁ →
        --     keepLeft (mapDirection g (fst x , snd x) y)
        --     (fromImpossibleRight (toImpossibleRight x₁)))
        -- ≡
        -- recoverLeft (forgetLeft (mapDirection g x y))
        -- (keepLeft (mapDirection g x y))


curryUncurry : {p q r : Polynomial} {g : Lens r (q ^ p)} → curry (uncurry₂ g) ≡ g -- uncurry₂ (curry g) ≡ g
curryUncurry {p} {q} {r} {g ⇆ g♯} = lensesEqual3 {!    !} {!   !} -- lensesEqual3 refl λ x y → {!   !}
    where
        yo : mapPosition (curry (uncurry₂ (g ⇆ g♯))) ≡ g
        yo = {!   !}
    -- where
    --     yo : (posR : position r) (posP : position p) → (λ x →
    --         forgetLeft
    --         (recoverLeft (snd (mapPosition g posR posP) x)
    --          (λ x₁ → mapDirection g posR (posP , x , help x₁))))
    --     yo = ?

eval-comp-simple : {C D E : Polynomial} → 
            (f : Lens (E * D) C) → 
            (eval ∘ₚ ⟨ curry f × idLens ⟩) -- same as uncurry₂ (curry f) = f
            ≡ f
eval-comp-simple {C} {D} {E} f = lensesEqual3 refl λ x y → {!   !}
    where
        easier : (x : position (E * D)) (y : direction C (mapPosition (eval ∘ₚ ⟨ curry f × idLens ⟩) x)) → mapDirection (eval ∘ₚ ⟨ curry f × idLens ⟩) x y ≡ mapDirection f x y
        easier x y = {!   !}


curry-unique-simple : {p q r : Polynomial} → {f : Lens p (q ^ r)} → {g : Lens (p * r) q} → eval ∘ₚ (⟨ f × idLens ⟩) ≡ g → f ≡ curry g
curry-unique-simple {p} {q} {r} {f} {g} pr = lensesEqual3 (funExt (λ x → funExt (λ y → {!  mapDirection g (x , y)  !}))) {!   !}

