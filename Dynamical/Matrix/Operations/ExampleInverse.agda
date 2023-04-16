{-# OPTIONS --guardedness #-}

module Dynamical.Matrix.Operations.ExampleInverse where

open import IO
open import Data.Unit
open import Dynamical.Matrix.Core
open import Dynamical.Matrix.Operations.PseudoInverse 
open import Data.Float renaming (Float to ℝ)
open import Function
open import Data.Vec

printMatrix : ∀ {n m} → Matrix ℝ n m → IO ⊤
printMatrix m = do
  putStr $ showMatrix m
  pure tt

exampleMatrix : Matrix ℝ 3 3
exampleMatrix = 𝕄 $
    (4.0 ∷  3.0 ∷  -1.0 ∷ []) ∷
    (5.0 ∷  3.0 ∷  2.0 ∷ []) ∷
    (2.0 ∷  1.0 ∷  3.0 ∷ []) ∷ []

examplePrint = run $ do
  putStr "Original matrix:\n"
  printMatrix exampleMatrix
  let inverted = exampleMatrix ⁻¹
  putStr "\nInverted matrix:\n"
  printMatrix inverted