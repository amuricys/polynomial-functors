{-# OPTIONS --cubical --sized-types #-}

module Cubical.Various where

open import Data.Bool
open import Data.Product
open import Data.Sum
open import CategoryData.Everything
open import Cubical.Core.Everything hiding (Σ-syntax)
open import Cubical.Foundations.Prelude hiding (Σ-syntax)
open import Cubical.Foundations.Isomorphism
open import Level
open import Cubical.PolynomialEquals
open import Cubical.LensEquality
open import Cubical.Data.Sigma.Properties
open import Data.Unit
open import Dynamical.System
open import Function

tupleToFunFromBool : {ℓ : Level} {A : Set ℓ} → (A × A) → Bool → A
tupleToFunFromBool (a , b) true = a
tupleToFunFromBool (a , b) false = b

sigmaBool≡tuple : {B : Bool → Set} → Σ Bool B ≡ ((B true) ⊎ (B false))
sigmaBool≡tuple = isoToPath (iso (λ {(false , snd₁) → inj₂ snd₁
                                    ; (true , snd₁) → inj₁ snd₁}) (λ {(inj₁ x) → true , x
                                                                    ; (inj₂ y) → false , y}) (λ {(inj₁ x) → refl
                                                                                                ; (inj₂ y) → refl}) λ {(false , snd₁) → refl
                                                                                                                    ; (true , snd₁) → refl})

coproductIsΣPoly : {p q : Polynomial} → ΣPoly (Bool , tupleToFunFromBool (p , q)) ≡ p + q
coproductIsΣPoly {p} {q} = poly≡∀' posEq dirEq
    where

        posEq : Polynomial.position ((ΣPoly (Bool , tupleToFunFromBool (p , q)))) ≡ Polynomial.position (p + q)
        posEq = sigmaBool≡tuple

        dirEq : (posA : Polynomial.position (ΣPoly (Bool , tupleToFunFromBool (p , q))))
            → Polynomial.direction ((ΣPoly (Bool , tupleToFunFromBool (p , q)))) posA ≡ subst (λ x → x → Type) (sym posEq) (Polynomial.direction (p + q)) posA
        dirEq (false , snd₁) = cong (Polynomial.direction q) (sym (transportRefl snd₁))
        dirEq (true , snd₁) = cong (Polynomial.direction p) (sym (transportRefl snd₁))

productIsΠPoly : {p q : Polynomial} → ΠPoly (Bool , tupleToFunFromBool (p , q)) ≡ (p * q) 
productIsΠPoly {p} {q} = poly≡∀' posEq dirEq
    where
        boolFun≡product : {B : Bool → Set} → ((index : Bool) → B index) ≡ (B true × B false)
        boolFun≡product = isoToPath (iso (λ x → x true , x false) (λ {x false → snd x
                                                                    ; x true → proj₁ x}) (λ b → refl) λ a → funExt λ {false → refl
                                                                                                                    ; true → refl})

        posEq : Polynomial.position (ΠPoly (Bool , tupleToFunFromBool (p , q))) ≡ Polynomial.position (p * q)
        posEq = boolFun≡product

        ⊎≡ : {A B C D : Set} → (A ≡ B) → (C ≡ D) → (A ⊎ C) ≡ (B ⊎ D)
        ⊎≡ p1 p2 i = p1 i ⊎ p2 i

        dirEq : (posA : Polynomial.position (ΠPoly (Bool , tupleToFunFromBool (p , q))))
            → Polynomial.direction ((ΠPoly (Bool , tupleToFunFromBool (p , q)))) posA ≡ subst (λ x → x → Type) (sym posEq) (Polynomial.direction (p * q)) posA
        dirEq x = sigmaBool≡tuple ∙ ⊎≡ (cong (Polynomial.direction p) (sym (transportRefl (x true)))) (cong (Polynomial.direction q) (sym (transportRefl (x false))))

-- They encode the same data
-- Question: do they also work similar, it seems I cant replace one with the other in fibonacci for instance. Maybe need other enclose and similar.
-- hej : (A B : Set) (f : A → B) → Iso (functionToDynamicalSystem A B f) (functionToDynamicalSystem₂ A B f)
-- hej A B f = {! isoToPath  !}

-- functionToDynamicalSystem₂ : {A B : Set} → (A → B) → DynamicalSystem
-- functionToDynamicalSystem₂ {A} {B} f = mkdyn A (monomial B A) (f ⇆ λ _ → id)

-- the arrow from 1 hack is to get around size issues, polys are bigger than sets
applyingIsSameAsComposingWithConstant : {r : Polynomial} → {A : Set} → Lens 𝟙 (r ◂ (Constant A)) ≡ r ⦅ A ⦆
applyingIsSameAsComposingWithConstant {r} {A} = isoToPath (iso go
                                                               back
                                                               (λ b → refl)
                                                               λ a → lens≡ₚ refl λ x () )
      where go : Lens 𝟙 (r ◂ (Constant A)) → r ⦅ A ⦆
            go (f ⇆ f♯) = f tt
            back : r ⦅ A ⦆ → Lens 𝟙 (r ◂ (Constant A))
            back (pos , md) = (λ _ → pos , md) ⇆ λ { fromPos () }