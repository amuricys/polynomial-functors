{-# OPTIONS --cubical #-}

module Categorical.Exponential where

open import Categorical.CubicalPoly
import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Common.CategoryData
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Categorical.Product
open import Categories.Object.Product Poly
import Categories.Category.CartesianClosed.Canonical as Canonical

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = MkPolynomial ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))
open import Cubical.PolynomialEquals
open import Cubical.Foundations.Prelude
open Polynomial
-- Exercise 4.29
p^0≡1 : {p : Polynomial} → p ^ Zero ≡ One
p^0≡1 {p} = poly≡∀' pos≡ dir≡
  where
    lemma : {A : ⊥ → Type} → ((i : ⊥) → A i) ≡ ⊤
    lemma = isoToPath (iso (λ x → tt) (λ {x ()}) (λ {tt → refl}) λ {a i ()})

    pos≡ : position (p ^ Zero) ≡ position One
    pos≡ =  lemma

    lemmaDir : {A : ⊥ → Type} → Σ ⊥ A ≡ ⊥
    lemmaDir = isoToPath (iso fst (λ {()}) (λ {()}) λ {()})

    dir≡ : (pos : position (p ^ Zero)) → direction (p ^ Zero) pos ≡ subst (λ x → x → Type) (sym pos≡) (direction One) pos
    dir≡ pos = lemmaDir

p^1≡p : {p : Polynomial} → p ^ One ≡ p
p^1≡p {p@(MkPolynomial pos dir)} = poly≡∀' pos≡ {!   !}
  where other : ((index : ⊤) → Σ pos (λ i → dir i → ⊤ ⊎ ⊥)) ≡ pos
        other = isoToPath (iso (λ x → fst (x tt)) (λ x tt → x , λ x₁ → inj₁ tt) (λ b → refl) λ a i index → fst (a tt) , λ x → {!   !})
        pos≡ : position (p ^ One) ≡ position p
        pos≡ = other
        


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

λg : {X A B : Polynomial} -> (X×A : Product X A) → Arrow (Product.A×B X×A) B → Arrow X (rtoq B A)  
λg {X} {A} {B} record { A×B = A×B ; π₁ = π₁ ; π₂ = π₂ ; ⟨_,_⟩ = ⟨_,_⟩ ; project₁ = project₁ ; project₂ = project₂ ; unique = unique } (mp ⇄ md) = let
  emp ⇄ emd = ev {A} {B}
  -- MkPolynomial h m = Product.A×B p
  -- hmm : position X -> position A -> position (X * A)
  -- hmm posX posA = posX , posA
  -- hmmm : position (X * A) -> position (Product.A×B (prod {X} {A}))
  -- hmmm p = p
  help : position A×B
  help = {!  !}
  in
  (\ x i → mp help , {!   !}) ⇄ {!   !} 

exp : {A B : Polynomial} -> Exponential A B
exp {A} {B} = record
    { B^A = rtoq B A
    ; product = prod
    ; eval = ev
    ; λg = \{X} X×A x → {!   !}
    ; β = {!   !}
    ; λ-unique = {!   !}
    }
 