{-# OPTIONS --cubical #-}

module AgdaCategories.Exponential where

open import AgdaCategories.CubicalPoly
import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Common.CategoryData
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import AgdaCategories.Product
open import Categories.Object.Product Poly

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = MkPolynomial ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))

rtoq : (r : Polynomial) -> (q : Polynomial) -> Polynomial
rtoq r (MkPolynomial posQ dirQ) = depProd (posQ , λ j → r ◂ (Y + Constant (dirQ j)))

-- Theorem 4.30
-- step1 : {p r q : Polynomial} -> Iso (Arrow p (rtoq r q)) (Arrow (p * q) r)
-- step1 {p} {r} {q} = iso one two three four
--   where -- dumbFunction : ((i₁ : position r) → direction r i₁ → ⊤ ⊎ direction q i) -> position r
--         -- dumbFunction f = ?
--         one : Arrow p (rtoq r q) → Arrow (p * q) r
--         one (mapPos ⇄ mapDir) = (λ { (fst₁ , snd₁) → let
--            xxx = mapPos fst₁ snd₁
--            yyy = mapDir fst₁
--            jeb : ((i : position r) → direction r i → ⊤ ⊎ direction q snd₁) -> position r
--            jeb f = {!   !}
--            in jeb xxx }) ⇄ {!   !}
--         two : Arrow (p * q) r → Arrow p (rtoq r q)
--         two (mapPos ⇄ mapDir) = (λ x i i₁ x₁ → {!   !}) ⇄ {!   !}
--         three : section one two
--         three = {!   !}
--         four : retract one two
--         four = {!   !}

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
λg {X} {A} {B} p (mp ⇄ md) = let
  emp ⇄ emd = ev {A} {B}
  -- MkPolynomial h m = Product.A×B p
  hmm : position X -> position A -> position (X * A)
  hmm posX posA = posX , posA
  hmmm : position (X * A) -> position (Product.A×B (prod {X} {A}))
  hmmm p = {!   !} , {!   !}
  in
  (\ x i → mp {!  !} , {!   !}) ⇄ {!   !} 

exp : {A B : Polynomial} -> Exponential A B
exp {A} {B} = record
    { B^A = rtoq B A
    ; product = prod
    ; eval = ev
    ; λg = λg
    ; β = {!   !}
    ; λ-unique = {!   !}
    }          