{-# OPTIONS --cubical #-}

module Categorical.CartesianClosed where

open import Categorical.CubicalPoly
import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Common.CategoryData
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (Σ-syntax ; curry)
open import Categorical.Product
open import Categories.Object.Product Poly
open import Categorical.Terminal
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
import Categories.Category.CartesianClosed.Canonical Poly as Canonical

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = MkPolynomial ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))

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
    ; _^_ = rtoq
    ; eval = ev
    ; curry = curry
    ; eval-comp =  {!   !}
    ; curry-resp-≈ = λ x → cong (λ a → curry a) x
    ; curry-unique = {!   !} -- λ x → {!   !}
    }
    where
        π₁ : {A : Polynomial} {B : Polynomial} → Arrow (A * B) A
        π₁ = fst ⇄ λ _ → inj₁
        π₂ : {A : Polynomial} {B : Polynomial} → Arrow (A * B) B
        π₂ = snd ⇄ λ _ → inj₂

        ⟨_,_⟩ : {A B C : Polynomial} → Arrow C A → Arrow C B → Arrow C (A * B)
        ⟨_,_⟩ = λ {(f ⇄ f♯) (g ⇄ g♯) → < f , g > ⇄ λ posC → [ f♯ posC , g♯ posC ]}

        helper : {p A B : Polynomial} {h : Arrow p (A * B)} -> ⟨ π₁ ∘p h , π₂ ∘p h ⟩ ≡ h
        helper {h = h} = arrowsEqual2 refl λ { x (inj₁ x1) → cong (λ zz → Arrow.mapDirection h x (inj₁ zz)) (sym (transportRefl  x1))
                                            ;  x (inj₂ y) → cong (λ zz → Arrow.mapDirection h x (inj₂ zz))  (sym (transportRefl y)) } -- λ i fromPos x → {!   !} -- (transportRefl {!   !} {!   !})

        unique : {F A B : Polynomial} {h : Arrow F (A * B)} {f₁ : Arrow F A} {f₂ : Arrow F B} →
            (π₁ ∘p h) ≡ f₁ →
            (π₂ ∘p h) ≡ f₂ → 
            ⟨ f₁ , f₂ ⟩ ≡ h
        unique {F = F} {h = h} p₁ p₂ = transitivity (λ i → ⟨ sym p₁ i , sym p₂ i ⟩) (helper {p = F} {h = h})

        rtoq : (r : Polynomial) -> (q : Polynomial) -> Polynomial
        rtoq r (MkPolynomial posQ dirQ) = depProd (posQ , λ j → r ◂ (Y + Constant (dirQ j)))

        ev : {A B : Polynomial} -> Arrow (rtoq B A * A) B
        ev {A} {B} = mp ⇄ md
            where mp : position (rtoq B A * A) → position B
                  mp (posB^A , posA) = fst (posB^A posA)
                  md : (fromPos : position (rtoq B A * A)) → direction B (mp fromPos) → direction (rtoq B A * A) fromPos
                  md (posB^A , posA) x with (snd (posB^A posA)) x in eq
                  ... | inj₂ v = inj₂ v
                  ... | inj₁ s = inj₁ (posA , x , help eq)
                          where help : (snd (posB^A posA) x) Eq.≡ inj₁ s -> [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posB^A posA) x)
                                help p rewrite p = tt
        
        curry : {C : Polynomial} {A : Polynomial} {B : Polynomial} → Arrow (C * A) B → Arrow C (rtoq B A)
        curry {C} {A} {B} f = mapPos ⇄ mapDir
            where
                module f = Arrow f

                mapPos : position C → position (rtoq B A)
                mapPos posC posA =  f.mapPosition (posC , posA) , lemma (f.mapDirection (posC , posA))
                    where
                        lemma : (direction B (f.mapPosition (posC , posA)) → direction (C * A) (posC , posA) ) → direction B (f.mapPosition (posC , posA)) → position (Y + Constant (direction A posA))
                        lemma f x with f x
                        ... | inj₁ x₁ = inj₁ tt
                        ... | inj₂ y = inj₂ y

                mapDir : (fromPos : position C) → direction (rtoq B A) (mapPos fromPos) → direction C fromPos
                mapDir posC (posA , fst , snd) with res <- (f.mapDirection (posC , posA) fst) in eq with res with snd 
                ... | inj₁ x | tt = x
                ... | inj₂ y | ()
        _×a_ : {A B C D : Polynomial} → (f : Arrow A C) (g : Arrow B D) → Arrow (A * B) (C * D)
        (mpf ⇄ mdf) ×a (mpg ⇄ mdg) = (λ {(a , b) → mpf a , mpg b}) ⇄ λ {(a , b) (inj₁ x) → inj₁ (mdf a x) 
                                                                      ; (a , b) (inj₂ y) → inj₂ (mdg b y) }
        eval-comp-simple : {A B C D E : Polynomial} → 
            (f : Arrow (E * D) C) → 
            (ev ∘p (curry f ×a idArrow))
              ≡ f
        eval-comp-simple (mp ⇄ md) = arrowsEqual3 refl λ x y → {!   !}
    -- eval-comp : {A B C : Polynomial} {f : Arrow (A * C) B} → ev ∘p (curry f ⁂ id) ≡ f
    -- eval-comp : {B A C f.B f.A.1 f.A.2 : Polynomial} {f : Arrow (A * C) B} → ev ∘p (curry f )
    --   (ev ∘p
    --    (record
    --     { product =
    --         record
    --         { A×B = A₁ * B₁
    --         ; π₁ = π₁
    --         ; π₂ = π₂
    --         ; ⟨_,_⟩ = λ {C} → ⟨_,_⟩
    --         ; project₁ = λ _ → π₁ ∘p ⟨ h , g ⟩
    --         ; project₂ = λ _ → π₂ ∘p ⟨ h , g ⟩
    --         ; unique = unique
    --         }
    --     }
    --     Categories.Category.Cartesian.BinaryProducts.⁂ curry f)
    --    idArrow)
    --   ≡ f
--         curry-unique : 