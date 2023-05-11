{-# OPTIONS --cubical #-}

module Categorical.Poly.Monoidal.Product where

open import Categorical.Poly.Instance
open import Categorical.Poly.Product
open import Cubical.Foundations.Prelude
open import Data.Product
open import Categories.Category.Monoidal
open import Categorical.Poly.Terminal
open import Cubical.LensEquality
import Categories.Category.Cartesian as Cartesian

binaryProducts : Cartesian.BinaryProducts Poly
binaryProducts = record { product = prod }

cartesian : Cartesian.Cartesian Poly
cartesian = record { terminal = terminalOne ; products = binaryProducts }

productMonoidal : Monoidal Poly
productMonoidal = Cartesian.CartesianMonoidal.monoidal Poly cartesian

open import Categories.Category.Monoidal.Symmetric productMonoidal
productSymmetricMonoidal : Symmetric
productSymmetricMonoidal = Cartesian.CartesianSymmetricMonoidal.symmetric Poly cartesian