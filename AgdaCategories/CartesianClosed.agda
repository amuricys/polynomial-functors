{-# OPTIONS --cubical #-}

module AgdaCategories.CartesianClosed where

open import AgdaCategories.CubicalPoly
import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Common.CategoryData
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (Σ-syntax ; curry)
open import AgdaCategories.Product
open import Categories.Object.Product Poly
open import AgdaCategories.Terminal
open import Cubical.Proofs
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
import Categories.Category.CartesianClosed.Canonical Poly as Canonical

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = MkPolynomial ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))

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

canonical : {A B : Polynomial} -> Canonical.CartesianClosed
canonical {A = A} {B = B} = let
   mp = 1
   
   in record
    { ⊤ = One
    ; _×_ = _*_
    ; ! = arrowToOne
    ; π₁ = fst ⇄ λ _ → inj₁
    ; π₂ = snd ⇄ λ _ → inj₂
    ; ⟨_,_⟩ = λ {(f ⇄ f♯) (g ⇄ g♯) → < f , g > ⇄ λ posC → [ f♯ posC , g♯ posC ]}
    ; !-unique = arrowToOneUnique
    ; π₁-comp = refl
    ; π₂-comp = refl
    ; ⟨,⟩-unique = λ x x₁ → {!  !}
    ; _^_ = rtoq
    ; eval = ev
    ; curry = curry
    ; eval-comp = {!   !}
    ; curry-resp-≈ = λ x → cong (λ a → curry a) x
    ; curry-unique = λ x → {!   !}
    }
    where
        π₁ = fst ⇄ λ _ → inj₁
        π₂ = snd ⇄ λ _ → inj₂

        ⟨_,_⟩ : {C : Polynomial} → Arrow C A → Arrow C B → Arrow C (A * B)
        ⟨_,_⟩ = λ {(f ⇄ f♯) (g ⇄ g♯) → < f , g > ⇄ λ posC → [ f♯ posC , g♯ posC ]}

        helper2 : {F : Polynomial} {h : Arrow F (A * B)} → (Arrow.mapDirection ⟨ π₁ ∘p h , π₂ ∘p h ⟩) ≡ Arrow.mapDirection h -- (λ posC → [ (λ z → Arrow.mapDirection h posC (inj₁ z)) , (λ z → Arrow.mapDirection h posC (inj₂ z)) ]) ≡ Arrow.mapDirection h --  {! λ posC → [ (λ z → Arrow.mapDirection h posC (inj₁ z)) , (λ z → Arrow.mapDirection h posC (inj₂ z)) ]) ≡ Arrow.mapDirection h  !} helper2 = {!   !}
        helper2 = funExt λ x → funExt λ {(inj₁ x) → refl
                                       ; (inj₂ y) → refl}

        helper : {p : Polynomial} {h : Arrow p (A * B)} -> ⟨ π₁ ∘p h , π₂ ∘p h ⟩ ≡ h
        -- helper {h = h} = arrowsEqual refl {! transportRefl helper2 !} -- λ i fromPos x → {!   !} -- (transportRefl {!   !} {!   !})
        helper {h = h} = arrowsEqual2 refl λ { x (inj₁ x1) → cong (λ zz → Arrow.mapDirection h x (inj₁ zz)) (sym (transportRefl  x1))
                                            ;  x (inj₂ y) → cong (λ zz → Arrow.mapDirection h x (inj₂ zz))  (sym (transportRefl y)) } -- λ i fromPos x → {!   !} -- (transportRefl {!   !} {!   !})

        helper22 : {p q : Polynomial} {f : Arrow p q} -> f ≡ f
        helper22 {f = f} = arrowsEqual refl (transportRefl (Arrow.mapDirection f))

        unique : {F : Polynomial} {h : Arrow F (A * B)} {f₁ : Arrow F A} {f₂ : Arrow F B} →
            (π₁ ∘p h) ≡ f₁ →
            (π₂ ∘p h) ≡ f₂ → 
            ⟨ f₁ , f₂ ⟩ ≡ h
        unique {F = F} {h = h} p₁ p₂ = transitivity (λ i → ⟨ sym p₁ i , sym p₂ i ⟩) (helper {p = F} {h = h})

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

                


--         curry : {C : Polynomial} {A = A₁ : Polynomial} {B = B₁ : Polynomial} → Arrow (C * A₁) B₁ → Arrow C (rtoq B₁ A₁)
--         curry {C} {A₁} {B₁} f = let
--             md = Arrow.mapDirection f
--             mp = Arrow.mapPosition f
--             in (λ x i → mp (x , i) , (λ x₁ →
--             {!   !} )) 
--             ⇄ 
--             λ {fromPos (fst₁ , fst₂ , snd₁) → let
--                 aa = md (fromPos , fst₁) fst₂
-- --                bb = md (fromPos , {!   !})
--                 in k fromPos fst₁ aa}
--                   where k : (fp : position C) (fst₁ : position A₁) -> direction (C * A₁) (fp , fst₁) -> direction C fp
--                         k fp fst₁ d with d 
--                         ... | inj₁ xx = xx
--                         ... | inj₂ xx = {!   !}
                
   