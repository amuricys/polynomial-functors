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
open import Cubical.Foundations.Path using ( toPathP⁻ )

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

-- 

-- Dynamical systems of form Sy^S → p is the same as p-coalgebra S → p(S)
-- See page 109 in poly book
isCoalgebra : {p : Polynomial} {S : Set} → Lens (selfMonomial S) p ≡ (S → p ⦅ S ⦆)
isCoalgebra {p} {S} = isoToPath (iso go back (λ _ → refl) (λ _ → refl))
    where
        go : Lens (selfMonomial S) p → S → p ⦅ S ⦆
        go (f ⇆ f♯) s = (f s) , (λ dir → f♯ s dir)

        back : (S → p ⦅ S ⦆) → Lens (selfMonomial S) p
        back coalgebra = (λ s → fst (coalgebra s)) ⇆ (λ s dir → snd (coalgebra s) dir)

-- Theorem 22 in https://arxiv.org/pdf/2202.00534.pdf
linearPolyCompPararell : {A : Set} {q : Polynomial} → linear A ◂ q ≡ linear A ⊗ q
linearPolyCompPararell {A} {q} = poly≡∀ pos≡ dir≡
    where
        lemma : {A : Set} → (⊤ → A) ≡ A
        lemma = isoToPath (iso (λ f → f tt) (λ a _ → a) (λ _ → refl) (λ _ → refl))

        pos≡ : position (linear A ◂ q) ≡ position (linear A ⊗ q)
        pos≡ = cong (Σ A) (funExt (λ x → lemma))

        dir≡ : ((posB : position (linear A ⊗ q) ) → subst (λ x → x → Type) pos≡ (direction (linear A ◂ q)) posB ≡ direction (linear A ⊗ q) posB)
        dir≡ (a , posQ) = cong (Σ ⊤) (funExt (λ _ → cong (direction q) (transportRefl posQ)))

apply : {A : Set} (f : A → Set) → {a₁ a₂ : A} (p : a₁ ≡ a₂) → (f a₁ ≡ f a₂)
apply f p i = f (p i) 

-- Also theorem 22 in https://arxiv.org/pdf/2202.00534.pdf
representablePolyCompPararell : {A : Set} {p : Polynomial} → p ◂ representable A ≡ p ⊗ representable A
representablePolyCompPararell {A} {p} = poly≡∀ pos≡ dir≡
    where
        lemma : {A : Set} → (A → ⊤) ≡ ⊤
        lemma = isoToPath (iso (λ _ → tt) (λ _ _ → tt) (λ _ → refl) (λ _ → refl))

        pos≡ : position (p ◂ representable A) ≡ position (p ⊗ representable A)
        pos≡ = cong (Σ (position p)) (funExt (λ _ → lemma))

        dir≡ : ((posB : position (p ⊗ representable A) ) → subst (λ x → x → Type) pos≡ (direction (p ◂ representable A)) posB ≡ direction (p ⊗ representable A) posB)
        dir≡ (posP , tt) = apply (λ a → Σ (direction p a) (λ x → A)) (transportRefl posP)

-- Helper
yi : {A C : Set} {B : A → Set} {D : C → Set} → ((Σ A B) ⊎ (Σ C D)) ≡ (Σ (A ⊎ C) λ {(inj₁ x) → B x
                                                                                ; (inj₂ y) → D y})
yi = isoToPath  (iso (λ {(inj₁ x) → (inj₁ (fst x)) , snd x 
                        ; (inj₂ y) → (inj₂ (fst y)) , (snd y)}) (λ {(inj₁ x , snd₁) → inj₁ (x , snd₁) 
                                                                    ; (inj₂ y , snd₁) → inj₂ (y , snd₁)}) (λ {(inj₁ x , snd₁) →  refl
                                                                                                            ; (inj₂ y , snd₁) → refl}) λ {(inj₁ x) → refl   
                                                                                                                                        ; (inj₂ y) → refl})
ΣLemma : {A B : Set} {C : A → Set} {D : B → Set} → (pr₁ : A ≡ B) → (C ≡ λ a → D (transport pr₁ a)) → Σ A C ≡ Σ B D
ΣLemma pr₁ pr₂ = cong (λ {(A , B) → Σ A B}) (ΣPathP (pr₁ , (toPathP⁻ pr₂)))

→≡ : {A B C D : Set} → A ≡ B → C ≡ D → (A → C) ≡ (B → D) 
→≡ p b i = p i → b i

prodDistOverComp : {p q r : Polynomial} → (p * q) ◂ r ≡ (p ◂ r) * (q ◂ r)
prodDistOverComp {p} {q} {r} = poly≡∀ (isoToPath (iso (λ x → ((fst (fst x)) , yo (snd x)) , (snd (fst x)) , ya (snd x)) (λ x → ((fst (fst x)) , fst (snd x)) , (snd (fst x) ++ (snd (snd x)))) (λ _ → refl) λ {(x , snd₁) → ΣPathP (refl , funExt (λ {(inj₁ x) → refl
                                                                                                                                                                                                                                        ; (inj₂ y) → refl})) })) λ {((fst₁ , snd₂) , fst₂ , snd₁) → ΣLemma (⊎≡ (cong (direction p) (transportRefl fst₁)) (cong (direction q) (transportRefl fst₂))) (funExt (λ {(inj₁ x) → cong (direction r) (transportRefl (snd₂
       (transp (λ j → direction p (transp (λ i → position p) j fst₁)) i0
        x))) 
                                                                                                                                                                                                                                                                                                                                                                                                              ; (inj₂ y) → cong (direction r) (transportRefl (snd₁
       (transp (λ j → direction q (transp (λ i → position q) j fst₂)) i0
        y)))})) ∙ sym yi}
    where
        yo : {A B C : Set} → (A ⊎ B → C) → (A → C)
        yo f = λ x → f (inj₁ x)

        ya : {A B C : Set} → (A ⊎ B → C) → (B → C)
        ya f = λ x → f (inj₂ x)

        _++_ : {A B C : Set} → (A → C) → (B → C) → (A ⊎ B → C)
        f ++ g = λ {(inj₁ x) → f x 
                  ; (inj₂ y) → g y}

        ye : {A B : Set} {a a₁ : A} {b b₁ : B} → (a ≡ a₁) → (b ≡ b₁) → (a , b) ≡ (a₁ , b₁)
        ye p b i = (p i , b i)



        ⊎≡ : {A B C D : Set} → (A ≡ B) → (C ≡ D) → (A ⊎ C) ≡ (B ⊎ D)
        ⊎≡ p1 p2 i = p1 i ⊎ p2 i

sumDistOverComp : {p q r : Polynomial} → (p + q) ◂ r ≡ (p ◂ r) + (q ◂ r)
sumDistOverComp {p} {q} {r} = poly≡∀ (isoToPath (iso (λ {(inj₁ x , snd₁) →  inj₁ (x , snd₁) 
                                                       ; (inj₂ y , snd₁) → inj₂ (y , snd₁)}) (λ {(inj₁ x) → (inj₁ (proj₁ x)) , (snd x)
                                                                                               ; (inj₂ y) → (inj₂ (proj₁ y)) , (snd y)}) (λ {(inj₁ x) → refl
                                                                                                                                           ; (inj₂ y) → refl}) λ {(inj₁ x , snd₁) →  refl 
                                                                                                                                                                ; (inj₂ y , snd₁) →  refl})) λ {(inj₁ x) → ΣLemma (cong (direction p) (transportRefl (proj₁ x))) (funExt (λ x₁ → cong (direction r) (transportRefl  (snd x
       (transp (λ j → direction p (transp (λ i → position p) j (proj₁ x)))
        i0 x₁))))) 
                                                                                                                                                                                              ; (inj₂ y) →  ΣLemma (cong (direction q) (transportRefl (proj₁ y))) (funExt (λ x → cong (direction r) (transportRefl (snd y
       (transp (λ j → direction q (transp (λ i → position q) j (proj₁ y)))
        i0 x)))))}