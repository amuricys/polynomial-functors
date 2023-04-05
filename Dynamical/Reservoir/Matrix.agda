
module Dynamical.Reservoir.Matrix where

open import Data.Nat using (ℕ)
open import Data.Float renaming (Float to ℝ) hiding (_+_ ; _*_)
import Data.Float as Float
import Data.Nat as Nat
open import Data.Vec as Vec hiding (sum ; map)


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

open Num {{...}}

numℕℝℝ : Num ℕ ℝ ℝ
Num._+_ numℕℝℝ = λ n x → fromℕ n Float.+ x
Num._*_ numℕℝℝ = λ n x → fromℕ n Float.* x
Num.zero numℕℝℝ = 0.0

numℝℕℝ : Num ℝ ℕ ℝ
Num._+_ numℝℕℝ = λ x n → x Float.+ fromℕ n
Num._*_ numℝℕℝ = λ x n → x Float.* fromℕ n
Num.zero numℝℕℝ = 0.0

numℝℝℝ : Num ℝ ℝ ℝ
Num._+_ numℝℝℝ = λ x n → x Float.+ n
Num._*_ numℝℝℝ = λ x n → x Float.* n
Num.zero numℝℝℝ = 0.0

instance
  numℝℝℝInstance : Num ℝ ℝ ℝ
  numℝℝℝInstance = numℝℝℝ
  

_+ᴹ_ : ∀ {A r c} {{numA : Num A A A}} → Matrix A r c → Matrix A r c → Matrix A r c
_+ᴹ_ {{numA = numA}} (record { values = m₁ }) (record { values = m₂ }) =
  record { values = zipWith (zipWith (Num._+_ numA)) m₁ m₂ }

_*ᴹs_ : ∀ {A r c} {{numA : Num A A A}} → Matrix A r c → A → Matrix A r c
_*ᴹs_ {{numA = numA}} (record { values = m }) a = record { values = Vec.map (Vec.map ((Num._*_ numA) a)) m }

_*ᴹ_ : ∀ {A r c p} {{numA : Num A A A}} → Matrix A r c → Matrix A c p → Matrix A r p
_*ᴹ_ {A = A} {p = p} {{numA = numA}} (record { values = m₁ }) (record { values = m₂ }) =
  record { values = Vec.map (λ row → Vec.map (λ col → sum (zipWith (Num._*_ numA) row col)) (transpose m₂)) m₁ }
  where
    sum : {a : ℕ} → Vec A a → A
    sum [] = Num.zero numA
    sum (x ∷ xs) = Num._+_ numA x (sum xs)
  
vecToColumnMatrix : ∀ {A} {n : ℕ} → Vec A n → Matrix A n 1
vecToColumnMatrix v = 𝕄 (Vec.map (λ x → [ x ]) v)

vecToRowMatrix : ∀ {A} {n : ℕ} → Vec A n → Matrix A 1 n
vecToRowMatrix v = 𝕄 [ v ]

transposeM : ∀ {A r c} → Matrix A r c → Matrix A c r
transposeM {A} {r} {c} (record { values = m }) = record { values = tabulate λ j → tabulate λ i → lookup (lookup m i) j }

map : ∀ {A B r c} → (A → B) → Matrix A r c → Matrix B r c
map f (𝕄 v) = 𝕄 (Vec.map ( λ r → Vec.map f r) v)