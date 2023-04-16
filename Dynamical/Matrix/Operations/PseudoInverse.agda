module Dynamical.Matrix.Operations.PseudoInverse where

open import Dynamical.Matrix.Core
open import Data.Float renaming (Float to ℝ)
open import Data.Nat
open import Data.List as L
open import Data.Vec as V hiding (_>>=_)
import Data.Maybe as M
open import Function
open import Relation.Binary.PropositionalEquality.TrustMe
open import Relation.Binary.PropositionalEquality


{-# FOREIGN GHC
import HsMatrix
#-}

postulate
  invertMatrixAsListTrusted : List (List ℝ) → List (List ℝ)
{-# COMPILE GHC invertMatrixAsListTrusted = invertMatrixAsList #-}

fl : ∀ {A : Set} {n} → (l : List A) → {l : L.length l ≡ n} → Vec A n
fl l {refl} = fromList l

fromListOfLists : ∀ {n m} → (l : List (List ℝ)) → {p₁ : L.length l ≡ n} → {p₂ : M.map L.length (L.head l) ≡ M.just m} → Matrix ℝ n m
fromListOfLists [] {refl} = 𝕄 []
fromListOfLists (x ∷ xs) {refl} {p} = 𝕄 (fl x {maybepr p} ∷ (V.map (\x → fl x {trustMe}) $ fl xs {trustMe}))
  where maybepr : ∀ {m n} → M.just m ≡ M.just n → m ≡ n
        maybepr refl = refl

_⁻¹ : ∀ {n : ℕ} → Matrix ℝ n n → Matrix ℝ n n
_⁻¹ {n} (𝕄 m) =
  let asList = toList $ V.map toList m
      inverted = invertMatrixAsListTrusted asList
  in fromListOfLists inverted {trustMe} {trustMe}
infixl 40 _⁻¹


-- Showing/displaying matrices
open import Data.String as S

showVec : ∀ {m} → Vec ℝ m → String 
showVec v = "[" S.++ go v S.++ "]"
  where go : ∀ {m} → Vec ℝ m → String
        go [] = ""
        go (x ∷ []) = Data.Float.show x
        go (x ∷ v) = Data.Float.show x S.++ ", " S.++ go v
 
showMatrix : ∀ {n m} → Matrix ℝ n m → String
showMatrix {.zero} {m} (𝕄 []) = ""
showMatrix {.(suc _)} {m} (𝕄 (v ∷ vs)) = showVec v S.++ "\n" S.++ showMatrix (𝕄 vs)
