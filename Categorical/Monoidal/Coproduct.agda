{-# OPTIONS --cubical #-}

module Categorical.Monoidal.Coproduct where

open import Categorical.Instance.Poly
open import Categorical.Initial
open import Categorical.Coproduct
open import Categories.Object.Coproduct Poly
open import Cubical.Proofs
open import Categories.Category.Monoidal
import Categories.Category.Cocartesian as Cocartesian

binaryCoproducts : Cocartesian.BinaryCoproducts Poly
binaryCoproducts = record { coproduct = coprod }

coproductCocartesian  : Cocartesian.Cocartesian Poly
coproductCocartesian = record { initial = initialZero ; coproducts = binaryCoproducts }

coproductMonodial : Monoidal Poly
coproductMonodial = Cocartesian.CocartesianMonoidal.+-monoidal Poly coproductCocartesian
