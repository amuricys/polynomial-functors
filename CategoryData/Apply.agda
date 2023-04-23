{-# OPTIONS --without-K #-}

module CategoryData.Apply where

open import CategoryData.Core
open import Data.Product
open import Data.Bool
open import Data.Unit
open import Function

-- Plug in a set: say you have p(y) = y^2 + 3. p ⦅ 2 ⦆ should return 2^2 + 3 ≅ 7
-- This is the action on objects (sets) of that polynomials perform as functors. They're (endo)functors after all.
_⦅_⦆ : Polynomial → Set → Set
_⦅_⦆ (mkpoly position direction) Y = Σ position λ x → (direction x → Y)


ex : Polynomial
ex = mkpoly Bool λ {false → Bool
                  ; true → ⊤}

f1 : ⊤ → Bool
f1 _ = true

f2 : ⊤ → Bool
f2 _ = false

some : ex ⦅ ⊤ ⦆
some = false , (λ{ false → tt
                 ; true → tt })

some2 : ex ⦅ ⊤ ⦆
some2 = true , id

-- Plug in a function: say you have p(y) = y^2 + 3 and f : 2 → 3. applyFn p f should return a function from 
-- the type 2^2 + 3 ≅ 7 to the type 3^2 + 3 ≅ = 12. This is the action on morphisms (functions) that polynomials
-- perform as functors (they are endofunctors in Set after all)
applyFn : {A B : Set} → (p : Polynomial) → (A → B) → p ⦅ A ⦆ → p ⦅ B ⦆
applyFn (mkpoly position direction) f (fst , snd) = fst , λ x → f (snd x)

fromLensInPolyToFunctionBetweenAppliedPolys : {p q : Polynomial} {S : Set} → Lens p q → p ⦅ S ⦆ → q ⦅ S ⦆
fromLensInPolyToFunctionBetweenAppliedPolys {(mkpoly pos dir)} {B} (mapPosition ⇆ mapDirection) (f , s) =
  mapPosition f , λ {x₁ → s (mapDirection f x₁)}
