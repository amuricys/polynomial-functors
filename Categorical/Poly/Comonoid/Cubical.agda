{-# OPTIONS --cubical  --without-K #-}
module Categorical.Poly.Comonoid.Cubical where

open import Cubical.Categories.Category
open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma.Properties
open import Cubical.LensEquality
open import Categorical.Poly.Monoidal.CompositionProduct hiding (assoc)
open import Data.Unit
open import Function renaming (id to idᶠ)
open import Level

record Comonoid : Set₁ where
  constructor Com
  field
    c : Polynomial
    ε : Lens c Y
    δ : Lens c (c ◂ c)
    coassoc : ⟨ idLens {c} ◂ δ ⟩ ∘ₚ δ ≡ transport (assoc⇆ {c}) (⟨ δ ◂ idLens {c} ⟩ ∘ₚ δ)
    leftCounit :  ~ᴸ ≡ ⟨ ε ◂ idLens {c} ⟩ ∘ₚ δ
    rightCounit : ~ᴿ ≡ ⟨ idLens {c} ◂ ε ⟩ ∘ₚ δ

comonoidsAreCategories : Comonoid → Category zero zero
comonoidsAreCategories (Com (em@(mkpoly pos dir)) (ε₁ ⇆ ε♯) (δ₁ ⇆ δ♯) coassoc leftCounit rightCounit) = cat
  where mpeq : (_, (λ _ → tt)) ≡ (λ x → fst (δ₁ x) , (λ a' → ε₁ (snd (δ₁ x) a')))
        mpeq = lens≡→mapPos≡ rightCounit
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
        Category._⋆_ cat {A} {B} {C} (dira , diraisb) (dirb , dirbisc) = {!   !} , {!   !}
                  --  δ♯ A ((subst dir (sym bookkeeping) dira) , 
                  --         subst dir (sym diraisb) dirb) , 
                  --        step1 ∙ dirbisc
            where ihavethis : let
                    -- lhs : {! position em → position (em ◂ em)  !}
                    lhs : Lens em (em ◂ (em ◂ em))
                    lhs = ((λ x → fst (δ₁ x) , (λ a' → δ₁ (snd (δ₁ x) a'))) ⇆
                            (λ i x → δ♯ i (fst x , δ♯ (snd (δ₁ i) (fst x)) (snd x))))
                    rhs : Lens em (em ◂ em ◂ em)
                    rhs = ((λ x → δ₁ (fst (δ₁ x)) , (λ a' → snd (δ₁ x) (δ♯ (fst (δ₁ x)) a')))
                          ⇆ (λ i x → δ♯ i (δ♯ (fst (δ₁ i)) (fst x) , snd x)))
                    in
                    lhs
                    ≡
                    transport assoc⇆ rhs
                  ihavethis = coassoc
                  mapPosEqDup : let
                    lhs : (position em → position (em ◂ (em ◂ em)))
                    lhs x = fst (δ₁ x) , (λ a' → δ₁ (snd (δ₁ x) a'))
                    rhs : position em → position (em ◂ em ◂ em)
                    rhs x = δ₁ (fst (δ₁ x)) , (λ a' → snd (δ₁ x) (δ♯ (fst (δ₁ x)) a'))
                    in
                    lhs
                    ≡
                    transport assocPos rhs
                  mapPosEqDup = lens≡→mapPos≡ coassoc
                  step1 : snd (δ₁ A)
                         (transport (λ i → dir (fst (mpeq i A)))
                         (δ♯ A
                          (transport (λ i → dir (fst (mpeq i A))) dira ,
                           transport (λ i → dir (diraisb (~ i))) dirb)))
                         ≡
                         snd (δ₁ B)
                              (transport (λ i → dir (fst (mpeq i B))) dirb)
                  step1 = {! (δ₁ A) !}
        Category.⋆IdL cat = {!   !}
        Category.⋆IdR cat = {!   !}
        Category.⋆Assoc cat = {!   !}
        Category.isSetHom cat = {!   !}

nestedTransportRefl : {A : Set} {a : A} → transp (λ _ → A) i0 (transp (λ _ → A) i0 a) ≡ a
nestedTransportRefl {a = a} = lem ∙ transportRefl a
  where lem : {B : Set} {b : B} → transp (λ _ → B) i0 b ≡ b
        lem {b = b} = transportRefl b

categoriesAreComonoids : Category zero zero → Comonoid
categoriesAreComonoids record { 
    ob = ob ;
    Hom[_,_] = Hom[_,_] ;
    id = id ;
    _⋆_ = _⋆_ ;
    ⋆IdL = idₗ ;
    ⋆IdR = idᵣ ;
    ⋆Assoc = ⋆Assoc ;
    isSetHom = isSetHom } = 
  Com emanator 
      ε
      δ -- transp (λ i → ob) i0 (transp (λ j → ob) i0 x)
      (lens≡ₚ (funExt (λ x → ΣPathP (sym nestedTransportRefl , toPathP {!   !}))) {!   !})
      (sym leftCounit)
      (sym rightCounit)
  where emanator : Polynomial
        emanator = mkpoly ob λ { dom → Σ[ cod ∈ ob ] Hom[ dom , cod ] }
        ε : Lens emanator Y
        ε = ((λ _ → tt) ⇆ λ { fromPos tt → fromPos , id })
        δ : Lens emanator (emanator ◂ emanator)
        δ = (λ x → x , fst) ⇆ λ { a ((b , froma) , (c , fromb)) → c , (froma ⋆ fromb) }
        
        rightCounit : ⟨ idLens ◂ ε ⟩ ∘ₚ δ ≡ ~ᴿ
        rightCounit = want
          where want : ((λ (x : ob) → x , (λ _ → tt)) ⇆
                        (λ (i : ob) (x : Σ (Σ ob (Hom[_,_] i)) (λ a → ⊤)) → fst (fst x) , (snd (fst x) ⋆ id)))
                       ≡ ((_, (λ _ → tt)) ⇆ (λ _ → fst))
                want = lens≡ₚ refl λ x y → ΣPathP ((transportRefl (fst (fst y))) , toPathP (dir≡ x y))
                  where dir≡ : (x : ob) → (y : Σ (Σ ob (Hom[_,_] x)) (λ a → ⊤)) → 
                              -- this is inverse constant transps along the same equality
                              transp (λ i → Hom[ x , transp (λ _ → ob) i (fst (fst y)) ])
                                i0
                                (transp (λ i → Hom[ x , transp (λ _ → ob) (~ i) (fst (fst y)) ])
                                i0 (snd (fst y))
                                ⋆ id)
                                ≡ snd (fst y)
                        dir≡ x y = removeConsts ∙ idᵣ (snd (fst y))
                          where removeConsts : transport (λ i → Hom[ x , transp (λ _ → ob) i (fst (fst y)) ])
                                  (transport (λ i → Hom[ x , transp (λ _ → ob) (~ i) (fst (fst y)) ])
                                  (snd (fst y)) ⋆ id)
                                  ≡
                                  (snd (fst y) ⋆ id)
                                removeConsts = {!   !} -- transport⁻Transport  {!   !} (snd (fst y) ⋆ id)
        leftCounit : ⟨ ε ◂ idLens ⟩ ∘ₚ δ ≡ ~ᴸ
        leftCounit = want
          where want :  
                    ((λ x → tt , (λ _ → x)) ⇆
                    (λ (i : ob) x → fst (snd x) , (id ⋆ snd (snd x))))
                    ≡ 
                    ((λ x → tt , (λ _ → x)) ⇆ 
                    (λ _ → snd))
                   
                want = lens≡ₚ refl λ x y → {!   !}

is : Comonoid ≡ Category zero zero
is = isoToPath (iso comonoidsAreCategories 
                    categoriesAreComonoids {!   !} {!   !})