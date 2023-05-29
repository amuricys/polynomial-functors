{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Cubical.Utils.CoproductUtils where

open import Data.Sum
open import Data.Empty
open import Cubical.Foundations.Everything hiding (id)
open import Cubical.Data.Sigma.Properties
open import Data.Unit
open import Cubical.Data.Sum.Properties
open import Function

variable
    A B : Type

forgetLeft : A ⊎ B → ⊤ ⊎ B
forgetLeft (inj₁ a) = inj₁ tt
forgetLeft (inj₂ b) = inj₂ b

recoverLeft : (x : ⊤ ⊎ B) → let isLeft = [ (λ _ → ⊤) , (λ _ → ⊥) ] x in (isLeft → A) → (A ⊎ B)
recoverLeft (inj₁ tt) generateA = inj₁ (generateA tt) 
recoverLeft (inj₂ b) generateA = inj₂ b

keepLeft : (x : A ⊎ B) → let isLeft = ([ (λ _ → ⊤) , (λ _ → ⊥) ] (forgetLeft x)) in isLeft → A
keepLeft (inj₁ a) pr = a
keepLeft (inj₂ b) ()

recoverForgetLeft : {x : A ⊎ B} → recoverLeft (forgetLeft x) (keepLeft x) ≡ x
recoverForgetLeft {x = inj₁ x} = refl
recoverForgetLeft {x = inj₂ y} = refl

forgetRecoverLeft : {x : ⊤ ⊎ B} {f : [ (λ _ → ⊤) , (λ _ → ⊥) ] x → A} → forgetLeft (recoverLeft x f) ≡ x
forgetRecoverLeft {x = inj₁ tt} = refl
forgetRecoverLeft {x = inj₂ y} = refl 

keepRecoverLeft : {A B : Set} {x : ⊤ ⊎ B} → {f : [ (λ _ → ⊤) , (λ _ → ⊥) ] x → A} → subst (λ h → [ (λ _ → ⊤) , (λ _ → ⊥) ] h → A) (forgetRecoverLeft {x = x}) (keepLeft (recoverLeft x f)) ≡ f
keepRecoverLeft {x = inj₁ tt} {f} = transportRefl f
keepRecoverLeft {x = inj₂ y} {f} = funExt (λ ())

-- Have Σ of forgotten left part, and a way to remember it, is the same as knowing it.
ΣforgetAndRememberSame : {A B : Set} → (Σ[ v ∈ (⊤ ⊎ B) ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] v → A)) ≡ (A ⊎ B)
ΣforgetAndRememberSame {A} {B} = isoToPath (iso go back p₁ p₂)
    where
        go : Σ[ v ∈ (⊤ ⊎ B) ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] v → A) → A ⊎ B
        go (v , gen) = recoverLeft v gen

        back : A ⊎ B → Σ[ v ∈ (⊤ ⊎ B) ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] v → A)
        back t = (forgetLeft t) , (keepLeft t)

        p₁ : (t : A ⊎ B) → recoverLeft (forgetLeft t) (keepLeft t) ≡ t
        p₁ t = recoverForgetLeft

        p₂ : (a : Σ[ v ∈ (⊤ ⊎ B) ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] v → A)) →
            (forgetLeft (recoverLeft (fst a) (snd a)) ,
            keepLeft (recoverLeft (fst a) (snd a)))
            ≡ a
        p₂ (v , gen) = ΣPathTransport→PathΣ (forgetLeft (recoverLeft v gen) , keepLeft (recoverLeft v gen)) (v , gen) (thing₁ , thing₂)
            where
                thing₁ : forgetLeft (recoverLeft v gen) ≡ v
                thing₁ = forgetRecoverLeft {x = v} {f = gen}

                thing₂ : subst (λ x → [ (λ _ → ⊤) , (λ _ → ⊥) ] x → A) (forgetRecoverLeft {x = v} {f = gen}) (keepLeft (recoverLeft v gen)) ≡ gen
                thing₂ = keepRecoverLeft {x = v} 


-- Below stuff are not criticial, but give intuition

⊎-disjoint : {x : A} {y : B} → inj₁ x ≡ inj₂ y → ⊥
⊎-disjoint path = subst (λ {(inj₁ x) → ⊤ ; (inj₂ x) → ⊥}) path tt

⊎-disjoint⁻ : {x : A} {y : B} → inj₂ x ≡ inj₁ y → ⊥
⊎-disjoint⁻ path = ⊎-disjoint (sym path)

-- Some intuition what the isLeft type means, (that the coproduct must be inj₁ tt)
fromImpossibleRight : {a : ⊤ ⊎ B} → [ (λ _ → ⊤) , (λ _ → ⊥) ] a → (a ≡ inj₁ tt)
fromImpossibleRight {a = inj₁ tt} term = refl

toImpossibleRight : {a : ⊤ ⊎ B} → (a ≡ inj₁ tt) → [ (λ _ → ⊤) , (λ _ → ⊥) ] a
toImpossibleRight {a = inj₁ tt} pr = tt
toImpossibleRight {a = inj₂ b} pr = ⊎-disjoint⁻ pr

fromToImpossibleRight : {a : ⊤ ⊎ B} {p : [ (λ _ → ⊤) , (λ _ → ⊥) ] a} → toImpossibleRight {a = a} (fromImpossibleRight p) ≡ p
fromToImpossibleRight {a = inj₁ tt} = refl

