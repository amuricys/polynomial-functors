{-# OPTIONS --cubical #-}

module Categorical.Poly.Exponential where

open import Categorical.Poly.Instance
import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import CategoryData.Everything
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Categorical.Poly.Product
open import Categories.Object.Product Poly
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Function using (_∘_ ; _$_)

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = mkpoly ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))
open import Cubical.PolynomialEquals
open import Cubical.Foundations.Prelude
open Polynomial
-- Exercise 4.29
p^0≡1 : {p : Polynomial} → p ^ 𝟘 ≡ 𝟙
p^0≡1 {p} = poly≡∀' pos≡ dir≡
  where
    lemma : {A : ⊥ → Type} → ((i : ⊥) → A i) ≡ ⊤
    lemma = isoToPath (iso (λ x → tt) (λ {x ()}) (λ {tt → refl}) λ {a i ()})

    pos≡ : position (p ^ 𝟘) ≡ position 𝟙
    pos≡ =  lemma

    lemmaDir : {A : ⊥ → Type} → Σ ⊥ A ≡ ⊥
    lemmaDir = isoToPath (iso fst (λ {()}) (λ {()}) λ {()})

    dir≡ : (pos : position (p ^ 𝟘)) → direction (p ^ 𝟘) pos ≡ subst (λ x → x → Type) (sym pos≡) (direction 𝟙) pos
    dir≡ pos = lemmaDir

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Foundations.HLevels

p^1≡p : {p : Polynomial} → p ^ 𝟙 ≡ p
p^1≡p {p@(mkpoly pos dir)} = poly≡' pos≡ dir≡
  where
      lemma₁ : {A : Type} → (⊤ → A) ≡ A
      lemma₁ = isoToPath (iso (λ x → x tt) (λ A tt → A) (λ b → refl) λ i → refl)

      lemma₄ : {A : Type} → (A → ⊤) ≡ ⊤
      lemma₄ = isoToPath (iso (λ x → tt) (λ x x₁ → tt) (λ b → refl) λ a → refl)
      
      lemma₃ : (⊤ ⊎ ⊥) ≡ ⊤
      lemma₃ = isoToPath (iso (λ x → tt) (λ x → inj₁ tt) (λ b → refl) λ {(inj₁ a) → refl ; (inj₂ ()) })

      lemma₂ : {A : Type} → (A → ⊤ ⊎ ⊥) ≡ ⊤
      lemma₂ {A} = (cong (λ x → (A → x)) lemma₃) ∙ lemma₄

      lemma₅ : {A : Type} → (Σ[ a ∈ A ] ⊤) ≡ A
      lemma₅ = isoToPath (iso fst (λ x → x , tt) (λ b → refl) λ a → refl)

      lemma : ((index : ⊤) → Σ pos (λ i → dir i → ⊤ ⊎ ⊥)) ≡ pos
      lemma = lemma₁ ∙ cong (λ a → Σ pos a) help ∙ lemma₅
        where
          help : (λ (pos : pos) → dir pos → ⊤ ⊎ ⊥) ≡ (λ (a : pos) → ⊤)
          help = funExt (λ x → lemma₂)

      pos≡ : position (p ^ 𝟙) ≡ position p
      pos≡ = lemma

      dir≡ : direction (p ^ 𝟙) ≡ (subst (λ x → x → Type) (sym pos≡) (direction p))-- ≡ direction p
      dir≡ = funExt λ {x → hej x}
        where
          hej : (x : position (mkpoly pos dir ^ 𝟙)) → direction (mkpoly pos dir ^ 𝟙) x ≡ subst (λ x₁ → x₁ → Type) (sym pos≡) dir x
          hej hej with hej tt in eq
          ... | fst₁ , snd₁ = {!   !}

rtoq : (r : Polynomial) → (q : Polynomial) → Polynomial
rtoq r (mkpoly posQ dirQ) = depProd (posQ , λ j → r ◂ (Y + Constant (dirQ j)))

ev : {A B : Polynomial} → Lens (rtoq B A * A) B
ev {A} {B} = mp ⇆ md
    where mp : position (rtoq B A * A) → position B
          mp (posB^A , posA) = fst (posB^A posA)
          md : (fromPos : position (rtoq B A * A)) → direction B (mp fromPos) → direction (rtoq B A * A) fromPos
          md (posB^A , posA) x with (snd (posB^A posA)) x in eq
          ... | inj₂ v = inj₂ v
          ... | inj₁ s = inj₁ (posA , x , help eq)
                where help : (snd (posB^A posA) x) Eq.≡ inj₁ s → [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posB^A posA) x)
                      help p rewrite p = tt

λg : {X A B : Polynomial} → (X×A : Product X A) → Lens (Product.A×B X×A) B → Lens X (rtoq B A)  
λg {X} {A} {B} record { A×B = A×B ; π₁ = π₁ ; π₂ = π₂ ; ⟨_,_⟩ = ⟨_,_⟩ ; project₁ = project₁ ; project₂ = project₂ ; unique = unique } (mp ⇆ md) = let
  emp ⇆ emd = ev {A} {B}
  -- mkpoly h m = Product.A×B p
  -- hmm : position X → position A → position (X * A)
  -- hmm posX posA = posX , posA
  -- hmmm : position (X * A) → position (Product.A×B (prod {X} {A}))
  -- hmmm p = p
  help : position A×B
  help = {!  !}
  in
  (\ x i → mp help , {!   !}) ⇆ {!   !} 

exp : {A B : Polynomial} → Exponential A B
exp {A} {B} = record
    { B^A = rtoq B A
    ; product = prod
    ; eval = ev
    ; λg = \ { {X} record { A×B = A×B ; π₁ = π₁ ; π₂ = π₂ ; ⟨_,_⟩ = ⟨_,_⟩ ; project₁ = project₁ ; project₂ = project₂ ; unique = unique } (f ⇆ f♯) → (λ x i → {! f  !}) ⇆ {!   !}}
    ; β = {!   !}
    ; λ-unique = {!   !}
    }
      