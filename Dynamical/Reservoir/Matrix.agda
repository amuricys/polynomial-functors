
module Dynamical.Reservoir.Matrix where

open import Data.Nat using (ℕ)
open import Data.Float renaming (Float to ℝ) hiding (_+_ ; _*_)
import Data.Float as Float
import Data.Nat as Nat
open import Data.Vec using (Vec ; tabulate ; zipWith ; _∷_ ; transpose ; [_] ; lookup ; [] )
import Data.Vec as Vec
open import Function

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
infixl 29 _+ᴹ_

_+ⱽ_ : ∀ {A n} {{numA : Num A A A}} → Vec A n → Vec A n → Vec A n
_+ⱽ_ {{numA = numA}} = zipWith (Num._+_ numA)
infixl 29 _+ⱽ_

_*ᴹs_ : ∀ {A r c} {{numA : Num A A A}} → Matrix A r c → A → Matrix A r c
_*ᴹs_ {{numA = numA}} (record { values = m }) a = record { values = Vec.map (Vec.map ((Num._*_ numA) a)) m }

_*ᴹ_ : ∀ {A r c p} {{numA : Num A A A}} → Matrix A r c → Matrix A c p → Matrix A r p
_*ᴹ_ {A = A} {p = p} {{numA = numA}} (record { values = m₁ }) (record { values = m₂ }) =
  record { values = Vec.map (λ row → Vec.map (λ col → sum (zipWith (Num._*_ numA) row col)) (transpose m₂)) m₁ }
  where
    sum : {a : ℕ} → Vec A a → A
    sum [] = Num.zero numA
    sum (x ∷ xs) = Num._+_ numA x (sum xs)
infixl 30 _*ᴹ_

vecToColumnMatrix : ∀ {A} {n : ℕ} → Vec A n → Matrix A n 1
vecToColumnMatrix v = 𝕄 (Vec.map (λ x → [ x ]) v)

vecToRowMatrix : ∀ {A} {n : ℕ} → Vec A n → Matrix A 1 n
vecToRowMatrix v = 𝕄 [ v ]

transposeM : ∀ {A r c} → Matrix A r c → Matrix A c r
transposeM {A} {r} {c} (record { values = m }) = record { values = tabulate λ j → tabulate λ i → lookup (lookup m i) j }

map : ∀ {A B r c} → (A → B) → Matrix A r c → Matrix B r c
map f (𝕄 v) = 𝕄 (Vec.map ( λ r → Vec.map f r) v)

rowToVec : ∀ {A} {n : ℕ} → Matrix A 1 n → Vec A n
rowToVec (𝕄 (v ∷ [])) = v

-- Might be too inefficient
columnToVec : ∀ {A} {n : ℕ} → Matrix A n 1 → Vec A n
columnToVec = rowToVec ∘ transposeM

_*ᴹⱽ_ : ∀ {A r c} {{numA : Num A A A}} → Matrix A r c → Vec A c → Vec A r
m *ᴹⱽ v = columnToVec (m *ᴹ vecToColumnMatrix v)
infixl 31 _*ᴹⱽ_

replicate : ∀ {A} → {r c : ℕ} → A → Matrix A r c
replicate a = 𝕄 (Vec.replicate (Vec.replicate a))

