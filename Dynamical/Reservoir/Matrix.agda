{-# OPTIONS --allow-unsolved-metas  #-}
module Dynamical.Reservoir.Matrix where

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

_ᵀ : ∀ {A r c} → Matrix A r c → Matrix A c r
(𝕄 m) ᵀ = 𝕄 (transpose m)
infixl 45 _ᵀ

transposeWorks : ∀ {one two thr} → _ᵀ
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

-- Might be too inefficient
columnMatrixToVec : ∀ {A} {n : ℕ} → Matrix A n 1 → Vec A n
columnMatrixToVec m = rowMatrixToVec (m ᵀ)

_*ᴹⱽ_ : ∀ {A r c} {{numA : Num A A A}} → Matrix A r c → Vec A c → Vec A r
m *ᴹⱽ v = columnMatrixToVec (m *ᴹ vecToColumnMatrix v)
infixl 31 _*ᴹⱽ_

replicate : ∀ {A} → {r c : ℕ} → A → Matrix A r c
replicate = 𝕄 ∘ Vec.replicate ∘ Vec.replicate

identity : ∀ {A} {n : ℕ} {{numA : Num A A A}} → Matrix A n n
identity  {n = n} {{numA = numA}} = 𝕄 (tabulate λ i → tabulate λ j → if ⌊ i ≟ j ⌋ then Num.one numA else Num.zero numA)

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

heee = maxIdx (-7.0 ∷ 1.0 ∷  2.0 ∷ 4.0 ∷  3.0 ∷ []) 

swapRows : ∀ {A} → {n m : ℕ} → Fin n → Fin n → Matrix A n m → Matrix A n m
swapRows i j mat@(𝕄 m) = 𝕄 (Vec.updateAt i (λ _ → lookup m j) (Vec.updateAt j (λ _ → lookup m i) m))

swapRowsWorks : ∀ {one two thr} → swapRows Fin.zero (Fin.suc Fin.zero) 
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

findPivot : ∀ {A m n} {{numA : Num A A A}} → (k : Fin (toℕ m +ℕ n)) → Matrix A (toℕ k +ℕ n) (toℕ k +ℕ n) → Fin (toℕ k +ℕ n)
findPivot {A} {n} {{numA}} k (𝕄 m) = {!   !}


-- luDecomposition : ∀ {A} {{numA : Num A A A}} → {n : ℕ} → Matrix A n n → LUP A n
-- luDecomposition {A} {{numA}} {n}  mat@(𝕄 m) = MkLUP l u p
--   where
--     step : Fin n → (Matrix A n n × Matrix A n n × Matrix A n n) → Matrix A n n × Matrix A n n × Matrix A n n
--     step k (𝕄 l , 𝕄 u , 𝕄 p) = (l' , u' , p')
--       where
--         -- Find the pivot index and swap the rows in P, L, and U
--         pivotIdx = maxIdx (Vec.map (λ row → Vec.drop (Fin.toℕ k) row) u)
--         p' = swapRows k pivotIdx p
--         u' = swapRows k pivotIdx u
--         l' = swapRows k pivotIdx (record { values = Vec.updateAt k (const (lookup l k Vec.++ (0 ∷ Vec.replicate k Num.zero numA))) l })
        
--         -- Perform Gaussian elimination
--         elim : ℕ → Matrix A n n → Matrix A n n
--         elim i u =
--           let
--             factor = Num._*_ numA (Num._*_ numA (Num.one numA) (lookup u i k)) (lookup u k k)
--           in
--             record { values = Vec.updateAt i (const (Vec.zipWith (Num._+_ numA) (lookup u i) (Vec.map (Num._*_ numA factor) (lookup u k)))) u }

--         -- Update U and L matrices
--         u'' = Vec.foldl elim u' (Vec.allFin n)
--         l'' = Vec.foldl (λ i l → record { values = Vec.updateAt i (const (Vec.updateAt k (const (lookup u i k)) (lookup l i))) l }) l' (Vec.allFin n)

--     -- Initialize L, U, and P matrices
--     u₀ = mat
--     l₀ = identity
--     p₀ = identity

--     -- Perform LU decomposition
--     lup : (Matrix A n n × Matrix A n n × Matrix A n n)
--     lup = Vec.foldl step (l₀ , u₀ , p₀) (Vec.allFin n)
--     l = proj₁ lup
--     u = proj₁ (proj₂ lup)
--     p = proj₂ (proj₂ lup)

_⁻¹ : ∀ {A} {{numA : Num A A A}} {n : ℕ} → Matrix A n n → Matrix A n n
_⁻¹ m = {!   !}
infixl 40 _⁻¹

pseudoinverse : ∀ {A r c} {{numA : Num A A A}} → A → Matrix A r c → Matrix A c r
pseudoinverse {A} {r} {c} {{numA = numA}} ridge m =
  let
    aTa = m ᵀ *ᴹ m
    aTaPlusLambdaI = aTa +ᴹ (identity *ᴹs ridge)
  in
    aTaPlusLambdaI ⁻¹ *ᴹ m ᵀ
  

-- Calculate the dot product of two vectors.
-- Define a function to update the output weights
updateOutputWeights :  {numNodes systemDim : ℕ} → OutputWeights numNodes systemDim → ℝ → Vec ℝ numNodes → Vec ℝ systemDim → OutputWeights numNodes systemDim
updateOutputWeights w learningRate state target = w + learningRate ⊗ (outerProduct (target - (w × state)) state)

-- Initialize the output weights to a zero matrix
initialOutputWeights :  {numNodes systemDim : ℕ} →  OutputWeights numNodes systemDim
initialOutputWeights = zeroMatrix systemDim numNodes

-- Define a learning rate (you can choose an appropriate value)
learningRate : ℝ
learningRate = 0.1

-- LMS algorithm for multiple iterations.
-- lmsAlgorithm : ∀ {n A} {{numA : Num A A A}} → A → Vec A n → Vec A n → Vec A n → Vec (A × Vec A n)
-- lmsAlgorithm μ w [] [] = []
-- lmsAlgorithm μ w (d ∷ ds) (x ∷ xs) =
--   let (e, w') = lmsIteration μ w d x
--   in (e , w') ∷ lmsAlgorithm μ w' ds xs
