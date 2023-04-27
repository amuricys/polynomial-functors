{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Utils.CoproductUtils where

open import Data.Sum
open import Data.Empty
open import Cubical.Foundations.Everything hiding (id)
open import Data.Unit
open import Function

variable
    A B : Type

⊎-disjoint : {x : A} {y : B} → inj₁ x ≡ inj₂ y → ⊥
⊎-disjoint path = subst (λ {(inj₁ x) → ⊤ ; (inj₂ x) → ⊥}) path tt

⊎-disjoint⁻ : {x : A} {y : B} → inj₂ x ≡ inj₁ y → ⊥
⊎-disjoint⁻ path = ⊎-disjoint (sym path)

absurd : ⊥ → A
absurd ()

forgetLeft : A ⊎ B → ⊤ ⊎ B
forgetLeft (inj₁ a) = inj₁ tt
forgetLeft (inj₂ b) = inj₂ b

forgetRight : A ⊎ B → A ⊎ ⊤
forgetRight (inj₁ a) = inj₁ a
forgetRight (inj₂ b) = inj₂ tt

recoverLeft : (x : ⊤ ⊎ B) → (x ≡ inj₁ tt → A) → (A ⊎ B)
recoverLeft (inj₁ tt) generateA = inj₁ (generateA refl)
recoverLeft (inj₂ b) generateA = inj₂ b

recoverRight : (x : A ⊎ ⊤) → (x ≡ inj₂ tt → B) → (A ⊎ B)
recoverRight (inj₁ a) generateB = inj₁ a
recoverRight (inj₂ tt) generateB = inj₂ (generateB refl)

keepLeft : (x : A ⊎ B) → (forgetLeft x ≡ inj₁ tt) → A
keepLeft (inj₁ a) pr = a
keepLeft (inj₂ b) pr = absurd (⊎-disjoint⁻ pr)

keepRight : (x : A ⊎ B) → (forgetRight x ≡ inj₂ tt) → B
keepRight (inj₁ a) pr = absurd (⊎-disjoint pr)
keepRight (inj₂ b) pr = b

recoverForgetLeft : {x : A ⊎ B} → recoverLeft (forgetLeft x) (keepLeft x) ≡ x
recoverForgetLeft {x = inj₁ x} = refl
recoverForgetLeft {x = inj₂ y} = refl

recoverForgetRight : {x : A ⊎ B} → recoverRight (forgetRight x) (keepRight x) ≡ x
recoverForgetRight {x = inj₁ x} = refl
recoverForgetRight {x = inj₂ y} = refl

forgetRecoverLeft : {x : ⊤ ⊎ B} {f : x ≡ inj₁ tt → A} → forgetLeft (recoverLeft x f) ≡ x
forgetRecoverLeft {x = inj₁ tt} = refl
forgetRecoverLeft {x = inj₂ y} = refl

forgetRecoverRight : (x : A ⊎ ⊤) (f : x ≡ inj₂ tt → A) → forgetRight (recoverRight x f) ≡ x
forgetRecoverRight (inj₁ x) f = refl
forgetRecoverRight (inj₂ tt) f = refl

lemma : {p : inj₁ {B = B} tt ≡ inj₁ tt} → (λ i → inj₁ tt) ≡ p
lemma {p = p} = {!   !}

keepRecoverLeft : {x : ⊤ ⊎ B} → {f : x ≡ inj₁ tt → B} → keepLeft (recoverLeft x f) ≡ subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f
keepRecoverLeft {x = inj₁ tt} {f} = funExt (λ x1 → cong f lemma) ∙ sym (transportRefl f)
keepRecoverLeft {x = inj₂ y} {f} = funExt (λ x → absurd (⊎-disjoint⁻ x)) ∙ sym (transportRefl f)

fromImpossibleRight : {a : ⊤ ⊎ B} → [ (λ _ → ⊤) , (λ _ → ⊥) ] a → (a ≡ inj₁ tt)
fromImpossibleRight {a = inj₁ tt} term = refl

toImpossibleRight : {a : ⊤ ⊎ B} → (a ≡ inj₁ tt) → [ (λ _ → ⊤) , (λ _ → ⊥) ] a
toImpossibleRight {a = inj₁ tt} pr = tt
toImpossibleRight {a = inj₂ b} pr = ⊎-disjoint⁻ pr

fromToImpossibleRight : {a : ⊤ ⊎ B} {p : [ (λ _ → ⊤) , (λ _ → ⊥) ] a} → toImpossibleRight {a = a} (fromImpossibleRight p) ≡ p
fromToImpossibleRight {a = inj₁ tt} = refl

toFromImpossibleRight : {a : ⊤ ⊎ B} {p : (a ≡ inj₁ tt)} → fromImpossibleRight (toImpossibleRight p) ≡ p
toFromImpossibleRight {a = inj₁ x} = lemma
toFromImpossibleRight {a = inj₂ y} {p = p} = absurd (⊎-disjoint⁻ p)

forgetMapLeft : {C : Type} {x : A ⊎ B} {f : A → C} → forgetLeft (map f id x) ≡ forgetLeft x
forgetMapLeft {x = inj₁ x} = refl
forgetMapLeft {x = inj₂ y} = refl


-- recoverLeft (forgetLeft (snd b dir))
--       (λ pr →
--          keepLeft (snd b dir) (fromImpossibleRight (toImpossibleRight pr)))
--       ≡ snd b dir

-- x = snd b dir

-- recoverLeft (forgetLeft x)
--       (λ pr →
--          keepLeft x (fromImpossibleRight (toImpossibleRight pr)))
--       ≡ x

-- (fromImpossibleRight (toImpossibleRight pr)) = pr

-- recoverLeft (forgetLeft x)
--       (λ pr →
--          keepLeft x pr)
--       ≡ x

-- eta-reduce

-- recoverLeft (forgetLeft x) (keepLeft x) ≡ x

-- recoverForgetLeft : {x : A ⊎ B} → recoverLeft (forgetLeft x) (keepLeft x) ≡ x
-- recoverForgetLeft {x = inj₁ x} = refl
-- recoverForgetLeft {x = inj₂ y} = refl
