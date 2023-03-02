{-# OPTIONS --cubical #-}

module AgdaCategories.Adjunction where

open import Categories.Adjoint
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open import Categories.NaturalTransformation renaming ( id to idN )
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Data.Equality
open import Cubical.Proofs
open import Function
open import Common.CategoryData
open import Data.Unit
open import Data.Empty
open import Data.Product
open import AgdaCategories.Functor.Constant
open import AgdaCategories.Functor.Linear
open import AgdaCategories.Functor.PlugInOne
open import AgdaCategories.Functor.PlugInZero
open import Level


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

id-⊥ : ⊥ → ⊥
id-⊥ x = x

!-⊥ : ⊥ → ⊥
!-⊥ ()

eq : id-⊥ ≡ !-⊥
eq i ()

eq2r : Path ((⊥ → ⊥) × (⊥ → ⊥)) (id-⊥ , id-⊥) (id-⊥ , !-⊥)
eq2r = cong′ (\x -> id-⊥ , x) (λ { i () })

{-
x != (λ ()) x of type ⊥
when checking the definition of eq2
-}

plugin1unit : NaturalTransformation idF (constantPolynomial ∘F plugIn1)
plugin1unit = record { 
    -- η =  λ X → (λ x → x , λ x₁ → tt) ⇄ λ fromPos () ;
    -- -- commute : ∀ {X Y} (f : C [ X , Y ]) → η Y ∘ F₁ f ≈ G.F₁ f ∘ η X
    -- commute = λ { {X} {Y} (mp ⇄ md) → let
    --   -- t = (fromPos : Polynomial.position X) -> ⊥ -> Polynomial.direction X fromPos
    --   pathToEq : {t : Type} {A B : t} -> Path t A B -> A ≡ B
    --   pathToEq {t} {A} {B} p = p
    --   summin : {fromPos : Polynomial.position X} -> ⊥ -> Polynomial.direction Y (mp fromPos)
    --   summin = \()
    --   summin2 : {fromPos : Polynomial.position X} -> ⊥ -> Polynomial.direction X fromPos
    --   summin2 = \()
    -- --   summin3 : (fromPos : Polynomial.position X) -> ⊥ -> Polynomial.direction X fromPos
    -- --   summin3 f = {!   !}
    --   thereIsPath : Path (((fromPos : Polynomial.position X) -> ⊥ -> Polynomial.direction X fromPos)) (λ fromPos z → md fromPos (summin z)) (λ fromPos z → summin2 z)
    --   thereIsPath = cong′ (\x -> {!   !}) refl
    --   in
    --   arrowsEqual refl {!   !} } ;
    -- sym-commute =  {!   !}
    η = λ X → (λ x → x , λ _ → tt) ⇄ λ fromPos () ;
    commute = λ f → arrowsEqual3 refl λ {x ()} ;
    sym-commute = λ f → arrowsEqual3 refl λ {x ()}
    }

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
                        