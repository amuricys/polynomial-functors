{-# OPTIONS --allow-unsolved-metas #-}

-- This module contains an attempt at doing matrix operations purely in Agda.
-- It is not used in the dynamical systems we operate on because these operations
-- are too slow, especially LUP decomposition and matrix inversion.

module Dynamical.Matrix.Operations.Experimental where

open import Dynamical.Matrix.Core
open import Dynamical.Matrix.Operations.Basic
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

maxIdx : ∀ {A n} {{numA : Num A A A}} → Vec A (suc n) → Fin (suc n)
maxIdx {A} {n} {{numA = numA}} v = proj₁ biggest
  where indicesAndValues : Vec (Fin (suc n) × A) (suc n)
        indicesAndValues = Vec.zip (Vec.allFin (suc n)) v
        step : Fin (suc n) × A → Fin (suc n) × A → Fin (suc n) × A
        step (biggestSoFarIndex , biggestSoFarValue) (curIndex , curValue) = 
          if Num._≤_ numA biggestSoFarValue curValue 
            then curIndex , curValue 
            else biggestSoFarIndex , biggestSoFarValue
        biggest = Vec.foldl₁ step indicesAndValues

sumPositiveProof : ∀ {k y} → k Nat.< k +ℕ suc y
sumPositiveProof {Nat.zero} {y} = Nat.s≤s Nat.z≤n
sumPositiveProof {suc k} {y} = Nat.s≤s sumPositiveProof

currentSubColumn : ∀ {A y} → {{numA : Num A A A}} → let n = suc y in (k : ℕ) →  Matrix A (k +ℕ n) (k +ℕ n) → Vec A n
currentSubColumn k (𝕄 m) = let
  mᵀ = Vec.transpose m
  currCol = Vec.lookup mᵀ (Fin.fromℕ< {k} sumPositiveProof)
  in
  Vec.drop k currCol

mat : ∀ {A : Set} {a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ : A}→ Matrix A 3 3
mat {_} {a₁₁} {a₁₂} {a₁₃} {a₂₁} {a₂₂} {a₂₃} {a₃₁} {a₃₂} {a₃₃} = 𝕄 $ 
  (a₁₁ ∷  a₁₂ ∷  a₁₃ ∷ []) ∷ 
  (a₂₁ ∷  a₂₂ ∷  a₂₃ ∷ []) ∷ 
  (a₃₁ ∷  a₃₂ ∷  a₃₃ ∷ []) ∷ []

hmm = maxIdx $ currentSubColumn 0 $ mat {ℝ} {4.0} {3.0} { -1.0} {5.0} {3.0} {2.0} {2.0} {1.0} {3.0}


toVecOfSum : ∀ {A : Set} {k y} → {p : k Nat.< (suc y)} → Vec A (suc y) → Vec A (k +ℕ suc (y ∸ k))
toVecOfSum {k = Nat.zero} {p = Nat.s≤s Nat.z≤n} v = v
toVecOfSum {k = suc m} {p = Nat.s≤s (Nat.s≤s p)} (x ∷ v) = x ∷ (toVecOfSum {k = m} {p = (Nat.s≤s p)} v)


toMatrixOfSum : ∀ {A : Set} {k y} → {p : k Nat.< (suc y)} → Matrix A (suc y) (suc y) → Matrix A (k +ℕ suc (y ∸ k)) (k +ℕ suc (y ∸ k))
toMatrixOfSum {p = p} (𝕄 v) = 𝕄 $ toVecOfSum {p = p} (Vec.map (toVecOfSum {p = p}) v)

toN< : {n : ℕ} → {k : Fin (suc n)} → toℕ k Nat.< suc n
toN< {Nat.zero} {Fin.zero} = Nat.s≤s Nat.z≤n
toN< {suc n} {Fin.zero} = Nat.s≤s Nat.z≤n
toN< {suc n} {Fin.suc k} = Nat.s≤s toN<


pr : ∀ {n} (k : Fin (suc n)) (maxind : Fin (suc (n ∸ toℕ k))) → toℕ k +ℕ toℕ maxind Nat.< suc n
pr {n} Fin.zero Fin.zero = Nat.s≤s Nat.z≤n
pr {suc n} Fin.zero (Fin.suc maxind) = Nat.s≤s (pr Fin.zero maxind )
pr {suc n} (Fin.suc k) maxind = Nat.s≤s (pr k maxind)

addBack : ∀ {n} → (k : Fin (suc n)) → Fin (suc (n ∸ toℕ k)) → Fin (suc n)
addBack k maxind = fromℕ< {(toℕ k +ℕ toℕ maxind)} (pr k maxind)
findPivot : ∀ {A n} {{numA : Num A A A}} → Matrix A (suc n) (suc n) → Fin (suc n) → Fin (suc n)
findPivot {A} {n} m k = let
  curSubCol = currentSubColumn (toℕ k) (toMatrixOfSum {A} {k = toℕ k} {y = n} {p = toN< {n} {k}} m)
  maxInd = maxIdx curSubCol
  in
  addBack k maxInd

hm = findPivot (mat {ℝ} 
   {16.0} {3.0} { 17.0} 
   {5.0} {3.0} {2.0} 
   {2.0} {4.0} {3.0}
   ) (Fin.suc Fin.zero)

swapRows : ∀ {A} → {n m : ℕ} → Fin n → Fin n → Matrix A n m → Matrix A n m
swapRows i j mat@(𝕄 m) = 𝕄 (Vec.updateAt i (λ _ → lookup m j) (Vec.updateAt j (λ _ → lookup m i) m))

swapRowsWorks : ∀ {A : Set} {one two thr : A} → swapRows Fin.zero (Fin.suc Fin.zero) 
  (𝕄 $
    (one ∷  one ∷  one ∷ []) ∷
    (two ∷  two ∷  two ∷ []) ∷
    (thr ∷  thr ∷  thr ∷ []) ∷ []
  ) ≡
  (𝕄 $
    (two ∷  two ∷  two ∷ []) ∷
    (one ∷  one ∷  one ∷ []) ∷
    (thr ∷  thr ∷  thr ∷ []) ∷ []
  )
swapRowsWorks = refl

-- LU decomposition
record LUP (A : Set) (n : ℕ) : Set where
  constructor MkLUP
  field
    L : Matrix A n n
    U : Matrix A n n
    P : Matrix A n n

luDecomposition : ∀ {A} {{numA : Num A A A}} {n : ℕ} → Matrix A (suc n) (suc n) → LUP A (suc n)
luDecomposition {A = A} {n = n} (𝕄 m) = fromAccType $ Vec.foldl (λ _ → AccType) step initLUP (Vec.allFin (suc n))
  where AccType : Set
        AccType = Matrix A (suc n) (suc n) × LUP A (suc n)
        fromAccType : AccType → LUP A (suc n)
        fromAccType = proj₂
        initLUP : AccType
        initLUP = 𝕄 m , MkLUP eye zeros eye
        step : AccType → Fin (suc n) → AccType
        step (mat@(𝕄 v) , MkLUP L U P) ind = newA ,  MkLUP L' U' P'
          where pivot = findPivot mat ind
                swappedA : Matrix A (suc n) (suc n)
                swappedA = swapRows ind pivot mat
                L' : Matrix A (suc n) (suc n)
                L' = {!   !}
                newA : Matrix A (suc n) (suc n)
                newA = {!   !}
                U' : Matrix A (suc n) (suc n)
                U' = {!   !}
                P' : Matrix A (suc n) (suc n)
                P' = swapRows ind pivot P

