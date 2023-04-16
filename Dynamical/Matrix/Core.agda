{-# OPTIONS --allow-unsolved-metas  #-}
module Dynamical.Matrix.Core where

open import Data.Nat using (ℕ ; _∸_  ; suc ) renaming (_+_ to _+ℕ_)
open import Data.Float renaming (Float to ℝ ; fromℕ to fromℕtoFloat) using (_÷_ ; _-_ )
import Data.Float as Float
import Data.Nat as Nat using (_≟_)
open import Data.Fin using (_≟_ ; fromℕ ; Fin ; fromℕ< ; toℕ)
import Data.Fin as Fin
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Data.Vec using (Vec ; tabulate ; zipWith ; _∷_ ; transpose ; [_] ; lookup ; [] )
import Data.Vec as Vec
open import Data.List using (List ; [] ; _∷_)
open import Function
open import Data.Bool using (if_then_else_ ; Bool ; true ; false)
open import Data.Maybe using (Maybe ; just ; nothing)
open import Data.List.Extrema
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)
open import Data.Product using (_×_ ; _,_ ; proj₁ ; proj₂)


record Matrix (A : Set) (rows cols : ℕ) : Set where
  constructor 𝕄
  field
    values : Vec (Vec A cols) rows
open Matrix

record Num (A B C : Set) : Set where
  field
    _+_ : A → B → C
    _*_ : A → B → C
    
    zero : C
    one : C
    _eq_ : C → C → Bool
    
    _≤_ : C → C → Bool
  infixl 19 _≤_
  infixl 19 _eq_
  infixl 20 _+_
  infixl 21 _*_

open Num {{...}}

numℕℝℝ : Num ℕ ℝ ℝ
Num._+_ numℕℝℝ = λ n x → fromℕtoFloat n Float.+ x
Num._*_ numℕℝℝ = λ n x → fromℕtoFloat n Float.* x
Num.zero numℕℝℝ = 0.0
Num.one numℕℝℝ = 1.0
Num._eq_ numℕℝℝ = λ n x → ⌊ n Float.≟ x ⌋
Num._≤_ numℕℝℝ = Float._≤ᵇ_

numℝℕℝ : Num ℝ ℕ ℝ
Num._+_ numℝℕℝ = λ x n → x Float.+ fromℕtoFloat n
Num._*_ numℝℕℝ = λ x n → x Float.* fromℕtoFloat n
Num.zero numℝℕℝ = 0.0
Num.one numℝℕℝ = 1.0
Num._eq_ numℝℕℝ = λ n x → ⌊ n Float.≟ x ⌋
Num._≤_ numℝℕℝ = Float._≤ᵇ_

numℝℝℝ : Num ℝ ℝ ℝ
Num._+_ numℝℝℝ = λ x n → x Float.+ n
Num._*_ numℝℝℝ = λ x n → x Float.* n
Num.zero numℝℝℝ = 0.0
Num.one numℝℝℝ = 1.0
Num._eq_ numℝℝℝ = λ n x → ⌊ n Float.≟ x ⌋
Num._≤_ numℝℝℝ = Float._≤ᵇ_

instance
  numℝℝℝInstance : Num ℝ ℝ ℝ
  numℝℝℝInstance = numℝℝℝ
