{-# OPTIONS --cubical #-}

module Categorical.Chart.Monoidal.Product where

open import Categorical.Chart.Instance
open import Categorical.Chart.Product
open import Cubical.Foundations.Prelude
open import Data.Product
open import Categorical.Chart.Terminal
open import Cubical.LensEquality
open import Categories.Category.Monoidal
import Categories.Category.Cartesian as Cartesian

binaryProducts : Cartesian.BinaryProducts ChartCat
binaryProducts = record { product = prod }

cartesian : Cartesian.Cartesian ChartCat
cartesian = record { terminal = terminalY ; 
                     products = binaryProducts }

productMonoidal : Monoidal ChartCat
productMonoidal 
    = Cartesian.CartesianMonoidal.monoidal ChartCat cartesian

open import Categories.Category.Monoidal.Symmetric productMonoidal
productSymmetricMonoidal : Symmetric
productSymmetricMonoidal 
    = Cartesian.CartesianSymmetricMonoidal.symmetric ChartCat cartesian