{-# OPTIONS --cubical #-}

module AgdaCategories.Adjunction where

open import Categories.Adjoint
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming ( id to idN )
open import Cubical.Foundations.Prelude
open import Cubical.Data.Equality
open import Cubical.Proofs
open import Function
open import Common.CategoryData
open import Data.Unit
open import AgdaCategories.Functor.Constant
open import AgdaCategories.Functor.Linear
open import AgdaCategories.Functor.PlugInOne
open import AgdaCategories.Functor.PlugInZero


-- Quadruple adjunction

constunit : NaturalTransformation idF (plugIn0 ∘F constantPolynomial)
constunit = record { 
    η = λ X x → x , id ; 
    commute = λ f → ctop refl ; 
    sym-commute = λ f → ctop refl }

constcounit : NaturalTransformation (constantPolynomial ∘F plugIn0) idF
constcounit = record { 
    η = λ X → fst ⇄ λ fromPos x → snd fromPos x ; 
    commute = λ {(aa ⇄ bb) i → (λ x → aa (fst x)) ⇄ λ fromPos x → snd fromPos (bb (fst fromPos) x) }; 
    sym-commute = λ f → refl }

constantPolynomial⊣plugIn0 : constantPolynomial ⊣ plugIn0 
constantPolynomial⊣plugIn0 = record 
    { unit = constunit
    ; counit = constcounit
    ; zig = refl
    ; zag = ctop refl }

plugin1unit : NaturalTransformation idF (constantPolynomial ∘F plugIn1)
plugin1unit = record { 
    η = λ X → (λ x → x , λ _ → tt) ⇄ λ fromPos () ;
    commute = λ f@(aa ⇄ bb) -> arrowsEqual refl {!   !} ; -- λ i fromPos x → fromAnythingToFalseToAnythingEqual i fromPos {!   !};
    sym-commute = λ f → arrowsEqual refl {!   !} } -- λ i fromPos x → fromAnythingToFalseToAnythingEqual i fromPos x }

plugin1counit : NaturalTransformation (plugIn1 ∘F constantPolynomial) idF
plugin1counit = record { 
    η = λ X x → fst x ; 
    commute = λ f → ctop refl ; 
    sym-commute = λ f → ctop refl }

plugIn1⊣constantPolynomial : plugIn1 ⊣ constantPolynomial
plugIn1⊣constantPolynomial = record 
    { unit = plugin1unit
    ; counit = plugin1counit
    ; zig = ctop refl
    ; zag = arrowsEqual refl fromAnythingToFalseToAnythingEqual}

linearunit : NaturalTransformation idF (plugIn1 ∘F linearPolynomial)
linearunit = record { 
    η = λ X x → x , λ _ → tt ; 
    commute = λ f → ctop refl ; 
    sym-commute = λ f → ctop refl }

linearcounit : NaturalTransformation (linearPolynomial ∘F plugIn1) idF
linearcounit = record { 
    η = λ X → (λ x → fst x) ⇄ λ fromPos x → tt ;
    commute = λ f → refl ;
    sym-commute = λ f → arrowsEqual refl (λ i fromPos x → tt) }

linearPolynomial⊣plugIn1 : linearPolynomial ⊣ plugIn1
linearPolynomial⊣plugIn1 = record 
    { unit = linearunit
    ; counit = linearcounit
    ; zig = refl
    ; zag = ctop refl }
               