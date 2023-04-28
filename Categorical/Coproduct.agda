{-# OPTIONS --cubical #-}

module Categorical.Coproduct where

open import Categorical.Instance.Poly
open import Categorical.Initial
open import Categories.Object.Coproduct Poly
open import CategoryData.Core
open import Data.Sum
open import Function
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Categories.Category.Monoidal
import Categories.Category.Cocartesian as Cocartesian
open import Cubical.LensEquality
open import CategoryData.Everything

coprod : {A B : Polynomial} → Coproduct A B
coprod {A = A} {B = B} = record
    { A+B = A + B
    ; i₁ = i₁
    ; i₂ = i₂
    ; [_,_] = [_,_]ₚ
    ; inject₁ = refl
    ; inject₂ = refl
    ; unique = unique
    }
    where
        open Lens
        open Polynomial

        helper : {p : Polynomial} {h : Lens (A + B) p} -> [ h ∘ₚ i₁ , h ∘ₚ i₂ ]ₚ ≡ h
        helper {p} {h} = lensesEqual3 (funExt λ {(inj₁ x) → refl
                                               ; (inj₂ y) → refl}) λ {(inj₁ x) y → cong (λ zz → mapDirection h (inj₁ x) zz) ((transportRefl y))
                                                                    ; (inj₂ y₁) y → cong (λ zz → mapDirection h (inj₂ y₁) zz) (transportRefl y)}

        unique : {F : Polynomial} {h : Lens (A + B) F} {f₁ : Lens A F} {f₂ : Lens B F} 
            → (h ∘ₚ i₁) ≡ f₁
            → (h ∘ₚ i₂) ≡ f₂
            → [ f₁ , f₂ ]ₚ ≡ h
        unique p₁ p₂ = (λ i → [ sym p₁ i , sym p₂ i ]ₚ) ∙ helper



-- univPropProdCoprod : {p q r : Polynomial} → Lens p (r ^ q) ≡ ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ◂ (Y + Constant (direction q j))))
-- univPropProdCoprod {p} {q} {r} = substed
--    where substed : Lens p (r ^ q) ≡ ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ◂ (Y + Constant (direction q j))))
--          substed = univPropCoproduct ∙ substed2
--             where lemma : ∀ {a b : position p → Type} → a ≡ b → ((i : position p) → a i) ≡ ((i : position p) → b i)
--                   lemma pr = cong (λ a₁ → (i : position p) → a₁ i) pr
--                   substed2 : ((i : position p) → Lens (purePower (direction p i)) (r ^ q))
--                                 ≡
--                              ((i : position p) (j : position q) → Lens (purePower (direction p i)) (r ◂ Y + Constant (direction q j)))
--                   substed2 = lemma (funExt λ x → univPropProduct {q = q})

-- Universal coproduct property. A function (A+B)→C is the same as two functions A→C and B→C
universalPropertyCoproduct : {p : Polynomial}
                               → Lens {!   !} p ≡ {!   !}
universalPropertyCoproduct = {!   !}

-- -- Universal product property. A function A→(B*C) is the same as two functions A→B and A→C
-- universalPropertyProduct : {p : Polynomial} {Index : Type} {generate : Index → Polynomial}
--                              → Lens p (ΠPoly (Index , generate)) ≡ ((i : Index) → Lens p (generate i))
-- universalPropertyProduct {p} {Index} {generate} = isoToPath (iso go back (λ b → refl) λ a → refl)
--     where
--         go : Lens p (ΠPoly (Index , generate)) → (i : Index) → Lens p (generate i)
--         go (f ⇆ f♯) index = (λ pos → f pos index) ⇆ λ pos dir → f♯ pos  (index , dir)

--         back : ((i : Index) → Lens p (generate i)) → Lens p (ΠPoly (Index , generate))
--         back generateLens = (λ pos index → mapPosition (generateLens index) pos) ⇆ λ {pos (index , dir) → mapDirection (generateLens index) pos dir}

