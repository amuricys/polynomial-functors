{-# OPTIONS --cubical  --without-K #-}
module Categorical.Poly.Comonoid.Core where

open import Data.Bool
open import Data.Unit
open import CategoryData.Polynomial

data Four : Set where a b c d : Four
data Five : Set where 𝟙 𝟚 𝟛 𝟜 𝟝 : Five

p : Polynomial
p = mkpoly Four λ { a → Five ; b → Bool ; c → Bool ; d → ⊤}

open import Categories.Category.Core
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
    assoc : ⟨ idLens {c} ◂ δ ⟩ ∘ₚ δ ≡ transport (assoc⇆ {c}) (⟨ δ ◂ idLens {c} ⟩ ∘ₚ δ)
    leftCounit :  ~ᴸ ≡ ⟨ ε ◂ idLens {c} ⟩ ∘ₚ δ
    rightCounit : ~ᴿ ≡ ⟨ idLens {c} ◂ ε ⟩ ∘ₚ δ


-- snd (mapPosition δ A)
--       (transp (λ i → dir (fst (mapPosition (rightCounit i) A))) i0
--        (mapDirection ε A tt))
--       ≡ A
comonoidsAreCategories : {emanator : Polynomial} → Comonoid emanator → Category zero zero zero
comonoidsAreCategories {em@(mkpoly pos dir)} (Com (ε₁ ⇆ ε♯) (δ₁ ⇆ δ♯) assoc leftCounit rightCounit) = cat
  where bookkeeping : {x : pos} → fst (δ₁ x) ≡ x
        bookkeeping {x} = funExt⁻ (sym (cong (fst ∘_) mpeq)) x -- use rightCounit
          where mpeq = lens≡→mapPos≡ rightCounit
        leftCoMpeq = lens≡→mapPos≡ leftCounit
        conged = cong (snd ∘_) leftCoMpeq
        need : (λ x _ → snd (δ₁ x) (ε♯ (fst (δ₁ x)) tt)) ≡ (λ x _ → x)
        need = sym conged
        -- thisworks? : {A : pos} → (transp (λ i → dir (fst (mapPosition (rightCounit i) A))) i0 (ε♯ A tt)) 
        --              ≡
        --              (ε♯ (fst (δ₁ i)) fromPos)
        thisworks? = {!   !}
        cod : ∀ {x} → dir x → pos
        cod {x} f = snd (δ₁ x) (subst dir (sym bookkeeping) f)
        cat : Category zero zero zero
        Category.Obj cat = pos 
        Category._⇒_ cat = λ x y → Σ[ f ∈ dir x ] (cod f ≡ y)
        Category._≈_ cat = _≡_
        Category.id cat {A} = ε♯ A tt , {! need  !}
        Category._∘_ cat {A} {B} {C} (dirb , dirbisc) (dira , diraisb) = 
                   δ♯ A ((subst dir (sym bookkeeping) dira) , 
                          subst dir (sym diraisb) dirb) , 
                         step1 ∙ dirbisc
            where step1 : snd (δ₁ A) 
                         (transport (λ i → dir (fst (mapPosition (rightCounit i) A)))
                         (δ♯ A
                          (transport (λ i → dir (fst (mapPosition (rightCounit i) A))) dira ,
                           transport (λ i → dir (diraisb (~ i))) dirb)))
                         ≡
                         snd (δ₁ B)
                              (transport (λ i → dir (fst (mapPosition (rightCounit i) B))) dirb)
                  step1 = {! assoc  !}

        Category.assoc cat = {!   !}
        Category.sym-assoc cat = {!   !}
        Category.identityˡ cat = {!   !}
        Category.identityʳ cat = {!   !}
        Category.identity² cat = {!   !}
        Category.equiv cat = {!   !}
        Category.∘-resp-≈ cat = {!   !}
-- categoriesAreComonoids : {emanator : Polynomial} → Category zero zero zero → Comonoid emanator
-- categoriesAreComonoids cat = {!   !}   