module Dynamical.Matrix.Operations.Basic where

open import Dynamical.Matrix.Core

open import Data.Nat using (ℕ ; _∸_  ; suc ) renaming (_+_ to _+ℕ_)
open import Data.Float renaming (Float to ℝ ; fromℕ to fromℕtoFloat) using (_÷_ ; _-_ )
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

open Num {{...}}


_+ᴹ_ : ∀ {A r c} {{numA : Num A A A}} → Matrix A r c → Matrix A r c → Matrix A r c
_+ᴹ_ {{numA = numA}} (record { values = m₁ }) (record { values = m₂ }) =
  record { values = zipWith (zipWith _+_) m₁ m₂ }
infixl 29 _+ᴹ_

_+ⱽ_ : ∀ {A n} {{numA : Num A A A}} → Vec A n → Vec A n → Vec A n
_+ⱽ_ {{numA = numA}} = zipWith _+_
infixl 29 _+ⱽ_

_*ᴹˢ_ : ∀ {A r c} {{numA : Num A A A}} → Matrix A r c → A → Matrix A r c
_*ᴹˢ_ {{numA = numA}} (record { values = m }) a = record { values = Vec.map (Vec.map (a *_)) m }
infixl 31 _*ᴹˢ_

_*ˢᴹ_ : ∀ {A r c} {{numA : Num A A A}} → A → Matrix A r c → Matrix A r c
_*ˢᴹ_ = flip _*ᴹˢ_
infixl 31 _*ˢᴹ_

_*ᴹ_ : ∀ {A r c p} {{numA : Num A A A}} → Matrix A r c → Matrix A c p → Matrix A r p
_*ᴹ_ {A = A} {p = p} {{numA = numA}} (record { values = m₁ }) (record { values = m₂ }) =
  record { values = Vec.map (λ row → Vec.map (λ col → sum (zipWith _*_ row col)) (transpose m₂)) m₁ }
  where
    sum : {a : ℕ} → Vec A a → A
    sum [] = zero
    sum (x ∷ xs) = x + (sum xs)
infixl 30 _*ᴹ_

vecToColumnMatrix : ∀ {A} {n : ℕ} → Vec A n → Matrix A n 1
vecToColumnMatrix v = 𝕄 (Vec.map (λ x → [ x ]) v)

vecToRowMatrix : ∀ {A} {n : ℕ} → Vec A n → Matrix A 1 n
vecToRowMatrix v = 𝕄 [ v ]

_ᵀ : ∀ {A r c} → Matrix A r c → Matrix A c r
(𝕄 m) ᵀ = 𝕄 (transpose m)
infixl 45 _ᵀ

transposeWorks : ∀ {A : Set} {one two thr : A} → _ᵀ
  (𝕄 $
    (one ∷  one ∷  one ∷ []) ∷
    (two ∷  two ∷  two ∷ []) ∷
    (thr ∷  thr ∷  thr ∷ []) ∷ []
  ) ≡
  (𝕄 $
    (one ∷  two ∷  thr ∷ []) ∷
    (one ∷  two ∷  thr ∷ []) ∷
    (one ∷  two ∷  thr ∷ []) ∷ []
  )
transposeWorks = refl

map : ∀ {A B r c} → (A → B) → Matrix A r c → Matrix B r c
map f (𝕄 v) = 𝕄 (Vec.map (Vec.map f) v)

rowMatrixToVec : ∀ {A} {n : ℕ} → Matrix A 1 n → Vec A n
rowMatrixToVec (𝕄 (v ∷ [])) = v

columnMatrixToVec : ∀ {A} {n : ℕ} → Matrix A n 1 → Vec A n
columnMatrixToVec m = rowMatrixToVec (m ᵀ)

_*ᴹⱽ_ : ∀ {A r c} {{numA : Num A A A}} → Matrix A r c → Vec A c → Vec A r
m *ᴹⱽ v = columnMatrixToVec (m *ᴹ vecToColumnMatrix v)
infixl 31 _*ᴹⱽ_

_*ⱽᴹ_ : ∀ {A r c} {{numA : Num A A A}} → Vec A c →  Matrix A r c → Vec A r
_*ⱽᴹ_ = flip _*ᴹⱽ_
infixl 31 _*ⱽᴹ_


replicate : ∀ {A} → {r c : ℕ} → A → Matrix A r c
replicate = 𝕄 ∘ Vec.replicate ∘ Vec.replicate

zeros : ∀ {A} → {r c : ℕ} → {{numA : Num A A A}} → Matrix A r c
zeros = replicate zero

eye : ∀ {A} {n : ℕ} {{numA : Num A A A}} → Matrix A n n
eye  {n = n} {{numA = numA}} = 𝕄 (tabulate λ i → tabulate λ j → if ⌊ i ≟ j ⌋ then one else zero)
