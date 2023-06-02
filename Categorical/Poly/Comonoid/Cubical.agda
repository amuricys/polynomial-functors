{-# OPTIONS --cubical  --without-K #-}
module Categorical.Poly.Comonoid.Cubical where

open import Cubical.Categories.Category
open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Cubical.LensEquality
open import Categorical.Poly.Monoidal.CompositionProduct hiding (assoc)
open import Data.Unit
open import Function

open import Level

record Comonoid (c : Polynomial) : Set where
  constructor Com
  field
    ε : Lens c Y
    δ : Lens c (c ◂ c)
    coassoc : ⟨ idLens {c} ◂ δ ⟩ ∘ₚ δ ≡ transport (assoc⇆ {c}) (⟨ δ ◂ idLens {c} ⟩ ∘ₚ δ)
    leftCounit :  ~ᴸ ≡ ⟨ ε ◂ idLens {c} ⟩ ∘ₚ δ
    rightCounit : ~ᴿ ≡ ⟨ idLens {c} ◂ ε ⟩ ∘ₚ δ

comonoidsAreCategories : {emanator : Polynomial} → Comonoid emanator → Category zero zero
comonoidsAreCategories {em@(mkpoly pos dir)} (Com (ε₁ ⇆ ε♯) (δ₁ ⇆ δ♯) coassoc leftCounit rightCounit) = cat
  where mpeq = lens≡→mapPos≡ rightCounit
        bookkeeping : {A : pos} → fst (δ₁ A) ≡ A
        bookkeeping {x} = funExt⁻ (sym (cong (fst ∘_) mpeq)) x
        leftCoMpeq = lens≡→mapPos≡ leftCounit
        conged = cong (snd ∘_) leftCoMpeq
        need : (λ A _ → snd (δ₁ A) (ε♯ (fst (δ₁ A)) tt)) ≡ (λ A _ → A)
        need = sym conged
        massagedNeed : (A : pos) → snd (δ₁ A) (ε♯ (fst (δ₁ A)) tt) ≡ A
        massagedNeed A = funExt⁻ (funExt⁻ (cong flip need) tt) A
        thisworks? : {A : pos} → 
                     transport (λ j → dir (fst (mpeq j A))) (ε♯ A tt) 
                     ≡
                     (ε♯ (fst (δ₁ A)) tt)
        thisworks? {A} i = transp (λ j → dir (fst (mpeq (i ∨ j) A))) i (ε♯ (bookkeeping (~ i)) tt)
        actualneed : {A : pos} →
                     snd (δ₁ A) (transp (λ i → dir (fst (mpeq i A))) i0 (ε♯ A tt))
                     ≡ 
                     A
        actualneed {A} = cong (snd (δ₁ A)) thisworks? ∙  massagedNeed A
        cod : ∀ {x} → dir x → pos
        cod {x} f = snd (δ₁ x) (subst dir (sym bookkeeping) f)
        cat : Category zero zero
        Category.ob cat = pos 
        Category.Hom[_,_] cat = λ x y → Σ[ f ∈ dir x ] (cod f ≡ y)
        Category.id cat {A} = ε♯ A tt , actualneed
        Category._⋆_ cat {A} {B} {C} (dira , diraisb) (dirb , dirbisc) = 
                   δ♯ A ((subst dir (sym bookkeeping) dira) , 
                          subst dir (sym diraisb) dirb) , 
                         step1 ∙ dirbisc
            where ihavethis : 
                    ((λ x → fst (δ₁ x) , (λ a' → δ₁ (snd (δ₁ x) a'))) ⇆
                      (λ i x → δ♯ i (fst x , δ♯ (snd (δ₁ i) (fst x)) (snd x))))
                    ≡
                    transport assoc⇆
                    ((λ x → δ₁ (fst (δ₁ x)) , (λ i₄ → snd (δ₁ x) (δ♯ (fst (δ₁ x)) i₄)))
                      ⇆ (λ i x → δ♯ i (δ♯ (fst (δ₁ i)) (fst x) , snd x)))
                  ihavethis = coassoc
                  -- verysimpleihave : 
                  --   ((λ x → fst (δ₁ x) , (λ a' → δ₁ (snd (δ₁ x) a'))) ⇆
                  --     (λ i x → δ♯ i (fst x , δ♯ (snd (δ₁ i) (fst x)) (snd x))))
                  --   ≡
                  --   transport someSimpleEquality
                  --   ((λ x → δ₁ (fst (δ₁ x)) , (λ i₄ → snd (δ₁ x) (δ♯ (fst (δ₁ x)) i₄)))
                  --     ⇆ (λ i x → δ♯ i (δ♯ (fst (δ₁ i)) (fst x) , snd x)))
                  -- verysimpleihave = ?
                  -- alsohavethis : 
                  --   (\x → (λ a' → δ₁ (snd (δ₁ x) a')))
                  --   ≡ 
                  --   transport {!   !}
                  --   (\x → (λ i₄ → snd (δ₁ x) (δ♯ (fst (δ₁ x)) i₄)))
                  -- alsohavethis = cong (snd ∘_ ) (lens≡→mapPos≡ ihavethis)
                  step1 : snd (δ₁ A)
                         (transport (λ i → dir (fst (mpeq i A)))
                         (δ♯ A
                          (transport (λ i → dir (fst (mpeq i A))) dira ,
                           transport (λ i → dir (diraisb (~ i))) dirb)))
                         ≡
                         snd (δ₁ B)
                              (transport (λ i → dir (fst (mpeq i B))) dirb)
                  step1 = {!  !}
        Category.⋆IdL cat = {!   !}
        Category.⋆IdR cat = {!   !}
        Category.⋆Assoc cat = {!   !}
        Category.isSetHom cat = {!   !}
-- categoriesAreComonoids : {emanator : Polynomial} → Category zero zero zero → Comonoid emanator
-- categoriesAreComonoids cat = {!   !}    