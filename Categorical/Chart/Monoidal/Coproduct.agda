{-# OPTIONS --cubical #-}

module Categorical.Chart.Monoidal.Coproduct where

open import Categorical.Chart.Instance
open import Categorical.Chart.Initial
open import Categorical.Chart.Coproduct
open import Categories.Object.Coproduct ChartCat
open import Cubical.Proofs
open import Categories.Category.Monoidal
import Categories.Category.Cocartesian as Cocartesian

binaryCoproducts : Cocartesian.BinaryCoproducts ChartCat
binaryCoproducts = record { coproduct = coprod }

coproductCocartesian  : Cocartesian.Cocartesian ChartCat
coproductCocartesian = record { initial = initialZero ;
                                coproducts = binaryCoproducts }

coproductMonoidal : Monoidal ChartCat
coproductMonoidal = 
  Cocartesian.CocartesianMonoidal.+-monoidal ChartCat coproductCocartesian

open import Categories.Category.Monoidal.Symmetric coproductMonoidal
productSymmetricMonoidal : Symmetric
productSymmetricMonoidal = 
  Cocartesian.CocartesianSymmetricMonoidal.+-symmetric ChartCat coproductCocartesian