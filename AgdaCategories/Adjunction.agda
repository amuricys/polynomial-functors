{-# OPTIONS --cubical #-}

module AgdaCategories.Adjunction where

open import Categories.Adjoint
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming ( id to idN )
open import Cubical.Foundations.Prelude

open import AgdaCategories.Functor.Constant
open import AgdaCategories.Functor.Linear
open import AgdaCategories.Functor.PlugInOne
open import AgdaCategories.Functor.PlugInZero


-- Quadruple adjunction

constantPolynomial⊣plugIn0 : constantPolynomial ⊣ plugIn0 
constantPolynomial⊣plugIn0 = record 
    { unit = {!   !}
    ; counit = {!   !}
    ; zig = {!   !}
    ; zag = {!   !} }

plugIn1⊣constantPolynomial : plugIn1 ⊣ constantPolynomial
plugIn1⊣constantPolynomial = record 
    { unit = {!   !}
    ; counit = {!   !}
    ; zig = {!   !}
    ; zag = {!   !} }

linearPolynomial⊣plugIn1 : linearPolynomial ⊣ plugIn1
linearPolynomial⊣plugIn1 = record 
    { unit = {!   !}
    ; counit = {!   !}
    ; zig = {!   !}
    ; zag = {!   !} }
           