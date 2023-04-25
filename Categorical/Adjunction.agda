{-# OPTIONS --cubical #-}

module Categorical.Adjunction where

open import Categories.Adjoint
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming ( id to idN )
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Data.Equality
open import Cubical.Proofs
open import Cubical.LensEquality
open import Function
open import CategoryData.Core
open import Data.Unit
open import Data.Empty
open import Data.Product
open import Categorical.Functor.Constant
open import Categorical.Functor.Linear
open import Categorical.Functor.PlugInOne
open import Categorical.Functor.PlugInZero
open import Level


-- Quadruple adjunction

constunit : NaturalTransformation idF (plugIn0 ∘F constantPolynomial)
constunit = record { 
    η = λ X x → x , id ; 
    commute = λ f → pathToEq refl ; 
    sym-commute = λ f → pathToEq refl }

constcounit : NaturalTransformation (constantPolynomial ∘F plugIn0) idF
constcounit = record { 
    η = λ X → fst ⇆ λ fromPos x → snd fromPos x ; 
    commute = λ {(aa ⇆ bb) i → (λ x → aa (fst x)) ⇆ λ fromPos x → snd fromPos (bb (fst fromPos) x) }; 
    sym-commute = λ f → refl }

constantPolynomial⊣plugIn0 : constantPolynomial ⊣ plugIn0 
constantPolynomial⊣plugIn0 = record 
    { unit = constunit
    ; counit = constcounit
    ; zig = refl
    ; zag = pathToEq refl }

id-⊥ : ⊥ → ⊥
id-⊥ x = x

!-⊥ : ⊥ → ⊥
!-⊥ ()

eq : id-⊥ ≡ !-⊥
eq i ()

eq2r : Path ((⊥ → ⊥) × (⊥ → ⊥)) (id-⊥ , id-⊥) (id-⊥ , !-⊥)
eq2r = cong′ (\x → id-⊥ , x) (λ { i () })

plugin1unit : NaturalTransformation idF (constantPolynomial ∘F plugIn1)
plugin1unit = record { 
    η = λ X → (λ x → x , λ _ → tt) ⇆ λ fromPos () ;
    commute = λ f → lens≡∀∀ refl λ {_ ()} ;
    sym-commute = λ f → lens≡∀∀ refl λ {_ ()}
    }

plugin1counit : NaturalTransformation (plugIn1 ∘F constantPolynomial) idF
plugin1counit = record { 
    η = λ X x → fst x ; 
    commute = λ f → pathToEq refl ; 
    sym-commute = λ f → pathToEq refl }

plugIn1⊣constantPolynomial : plugIn1 ⊣ constantPolynomial
plugIn1⊣constantPolynomial = record 
    { unit = plugin1unit
    ; counit = plugin1counit
    ; zig = pathToEq refl
    ; zag = lens≡∀∀ refl λ {fromPos ()} }

linearunit : NaturalTransformation idF (plugIn1 ∘F linearPolynomial)
linearunit = record { 
    η = λ X x → x , λ _ → tt ; 
    commute = λ f → pathToEq refl ; 
    sym-commute = λ f → pathToEq refl }

linearcounit : NaturalTransformation (linearPolynomial ∘F plugIn1) idF
linearcounit = record { 
    η = λ X → (λ x → fst x) ⇆ λ fromPos x → tt ;
    commute = λ f → refl ;
    sym-commute = λ f → lens≡ refl λ i fromPos x → tt }

linearPolynomial⊣plugIn1 : linearPolynomial ⊣ plugIn1
linearPolynomial⊣plugIn1 = record 
    { unit = linearunit
    ; counit = linearcounit
    ; zig = refl
    ; zag = pathToEq refl }
                        