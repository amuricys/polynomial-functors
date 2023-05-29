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

recoverLeft' : (x : ⊤ ⊎ B) → ([ (λ _ → ⊤) , (λ _ → ⊥) ] x → A) → (A ⊎ B)
recoverLeft' (inj₁ tt) generateA = inj₁ (generateA tt) 
recoverLeft' (inj₂ b) generateA = inj₂ b -- inj₂ b

recoverRight : (x : A ⊎ ⊤) → (x ≡ inj₂ tt → B) → (A ⊎ B)
recoverRight (inj₁ a) generateB = inj₁ a
recoverRight (inj₂ tt) generateB = inj₂ (generateB refl)

keepLeft : (x : A ⊎ B) → (forgetLeft x ≡ inj₁ tt) → A
keepLeft (inj₁ a) pr = a
keepLeft (inj₂ b) pr = absurd (⊎-disjoint⁻ pr)

keepLeft' : (x : A ⊎ B) → ([ (λ _ → ⊤) , (λ _ → ⊥) ] (forgetLeft x)) → A
keepLeft' (inj₁ a) pr = a -- a
keepLeft' (inj₂ b) () -- pr = {!   !} -- absurd (⊎-disjoint⁻ pr)

keepRight : (x : A ⊎ B) → (forgetRight x ≡ inj₂ tt) → B
keepRight (inj₁ a) pr = absurd (⊎-disjoint pr)
keepRight (inj₂ b) pr = b

recoverForgetLeft : {x : A ⊎ B} → recoverLeft (forgetLeft x) (keepLeft x) ≡ x
recoverForgetLeft {x = inj₁ x} = refl
recoverForgetLeft {x = inj₂ y} = refl

recoverForgetLeft' : {x : A ⊎ B} → recoverLeft' (forgetLeft x) (keepLeft' x) ≡ x
recoverForgetLeft' {x = inj₁ x} = refl -- refl
recoverForgetLeft' {x = inj₂ y} = refl -- refl

recoverForgetRight : {x : A ⊎ B} → recoverRight (forgetRight x) (keepRight x) ≡ x
recoverForgetRight {x = inj₁ x} = refl
recoverForgetRight {x = inj₂ y} = refl

forgetRecoverLeft : {x : ⊤ ⊎ B} {f : x ≡ inj₁ tt → A} → forgetLeft (recoverLeft x f) ≡ x
forgetRecoverLeft {x = inj₁ tt} = refl
forgetRecoverLeft {x = inj₂ y} = refl

forgetRecoverLeft' : {x : ⊤ ⊎ B} {f : [ (λ _ → ⊤) , (λ _ → ⊥) ] x → A} → forgetLeft (recoverLeft' x f) ≡ x
forgetRecoverLeft' {x = inj₁ tt} = refl -- refl
forgetRecoverLeft' {x = inj₂ y} = refl 

forgetRecoverLeft2' : (x : ⊤ ⊎ B) (f : [ (λ _ → ⊤) , (λ _ → ⊥) ] x → A) → forgetLeft (recoverLeft' x f) ≡ x
forgetRecoverLeft2' (inj₁ tt) _ = refl -- refl
forgetRecoverLeft2' (inj₂ y) _ = refl 

forgetRecoverLeft2 : (x : ⊤ ⊎ B) (f : x ≡ inj₁ tt → A) → forgetLeft (recoverLeft x f) ≡ x
forgetRecoverLeft2 (inj₁ tt) f = refl
forgetRecoverLeft2 (inj₂ y) f = refl

forgetRecoverRight : (x : A ⊎ ⊤) (f : x ≡ inj₂ tt → A) → forgetRight (recoverRight x f) ≡ x
forgetRecoverRight (inj₁ x) f = refl
forgetRecoverRight (inj₂ tt) f = refl

-- lemma : {p : inj₁ {B = B} tt ≡ inj₁ tt} → (λ i → inj₁ tt) ≡ p
-- lemma {B} {p = p} = {! isEmbedding-inl   !}

-- keepRecoverLeft : {x : ⊤ ⊎ B} → {f : x ≡ inj₁ tt → B} → keepLeft (recoverLeft x f) ≡ subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f
-- keepRecoverLeft {x = inj₁ tt} {f} = funExt (λ x1 → cong f lemma) ∙ sym (transportRefl f)
-- keepRecoverLeft {x = inj₂ y} {f} = funExt (λ x → absurd (⊎-disjoint⁻ x)) ∙ sym (transportRefl f)

keepRecoverLeft' : {x : ⊤ ⊎ B} → {f : [ (λ _ → ⊤) , (λ _ → ⊥) ] x → B} → keepLeft' (recoverLeft' x f) ≡ subst (λ a → ([ (λ _ → ⊤) , (λ _ → ⊥) ] a) → B) (sym (forgetRecoverLeft' {x = x})) f -- subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f
keepRecoverLeft' {x = inj₁ tt} {f} = funExt (λ tt → sym (transportRefl (f tt))) -- funExt (λ x1 → cong f lemma) ∙ sym (transportRefl f)
keepRecoverLeft' {x = inj₂ y} {f} = funExt (λ ()) -- funExt (λ x → absurd (⊎-disjoint⁻ x)) ∙ sym (transportRefl f)

keepRecoverLeft'' : {x : ⊤ ⊎ B} → {f : [ (λ _ → ⊤) , (λ _ → ⊥) ] x → B} → subst (λ h → [ (λ _ → ⊤) , (λ _ → ⊥) ] h → B) (forgetRecoverLeft' {x = x}) (keepLeft' (recoverLeft' x f)) ≡ f -- {! subst (λ p → [ (λ _ → ⊤) , (λ _ → ⊥) ] p → B) forgetRecoverLeft' keepLeft' (recoverLeft' x f)  !} ≡ f --  keepLeft' (recoverLeft' x f) ≡ {!  f !} -- subst (λ a → ([ (λ _ → ⊤) , (λ _ → ⊥) ] a) → B) (sym (forgetRecoverLeft' {x = x})) f -- subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f
keepRecoverLeft'' {x = inj₁ tt} {f} = transportRefl f -- funExt (λ tt → sym (transportRefl (f tt))) -- funExt (λ x1 → cong f lemma) ∙ sym (transportRefl f)
keepRecoverLeft'' {x = inj₂ y} {f} = funExt (λ ()) -- funExt (λ ()) -- funExt (λ x → absurd (⊎-disjoint⁻ x)) ∙ sym (transportRefl f)

keepRecoverLeft''' : {A B : Set} {x : ⊤ ⊎ B} → {f : [ (λ _ → ⊤) , (λ _ → ⊥) ] x → A} → subst (λ h → [ (λ _ → ⊤) , (λ _ → ⊥) ] h → A) (forgetRecoverLeft' {x = x}) (keepLeft' (recoverLeft' x f)) ≡ f -- {! subst (λ p → [ (λ _ → ⊤) , (λ _ → ⊥) ] p → B) forgetRecoverLeft' keepLeft' (recoverLeft' x f)  !} ≡ f --  keepLeft' (recoverLeft' x f) ≡ {!  f !} -- subst (λ a → ([ (λ _ → ⊤) , (λ _ → ⊥) ] a) → B) (sym (forgetRecoverLeft' {x = x})) f -- subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f
keepRecoverLeft''' {x = inj₁ tt} {f} = transportRefl f -- funExt (λ tt → sym (transportRefl (f tt))) -- funExt (λ x1 → cong f lemma) ∙ sym (transportRefl f)
keepRecoverLeft''' {x = inj₂ y} {f} = funExt (λ ()) -- funExt (λ ()) -- funExt (λ x → absurd (⊎-disjoint⁻ x)) ∙ sym (transportRefl f)


-- keepRecoverLeft2 : {x : ⊤ ⊎ B} {f : x ≡ inj₁ tt → B} {a : forgetLeft (recoverLeft x f) ≡ inj₁ tt}
--     → keepLeft (recoverLeft x f) a ≡ f (subst (λ h → h ≡ inj₁ tt) forgetRecoverLeft a)
-- keepRecoverLeft2 {x = inj₁ x} {f = f} {a = a} = cong f (sym (transportRefl a ∙ sym lemma))
-- keepRecoverLeft2 {x = inj₂ y} {f = f} {a = a} = absurd (⊎-disjoint⁻ a)

-- keepRecoverLeft3 : {x : ⊤ ⊎ B} → {f : x ≡ inj₁ tt → B} → keepLeft (recoverLeft x f) ≡ λ x → subst (λ _ → B) (sym forgetRecoverLeft) (f (subst (λ x₂ → x₂ ≡ inj₁ tt) forgetRecoverLeft x)) -- subst (λ _ → B) (sym forgetRecoverLeft) (subst (λ a → {! a ≡ inj₁ tt  !}) forgetRecoverLeft x) -- subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f
-- keepRecoverLeft3 = {!   !}

-- keepRecoverLeft4 : {x : ⊤ ⊎ B} → {f : x ≡ inj₁ tt → B} → keepLeft (recoverLeft x f) ≡ λ x → f (subst (λ x₂ → x₂ ≡ inj₁ tt) forgetRecoverLeft x) -- subst (λ _ → B) (sym forgetRecoverLeft) (subst (λ a → {! a ≡ inj₁ tt  !}) forgetRecoverLeft x) -- subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f
-- keepRecoverLeft4 {x = inj₁ x} {f = f} = funExt (λ x → cong f (lemma ∙ sym (transportRefl x)))
-- keepRecoverLeft4 {x = inj₂ y} {f = f} = funExt (λ x → absurd (⊎-disjoint⁻ x))

-- keepRecoverLeft5 : {x : ⊤ ⊎ B} → {f : x ≡ inj₁ tt → B} {a : forgetLeft (recoverLeft x f) ≡ inj₁ tt} → keepLeft (recoverLeft x f) a ≡ f (subst (λ x₂ → x₂ ≡ inj₁ tt) forgetRecoverLeft a) -- subst (λ _ → B) (sym forgetRecoverLeft) (subst (λ a → {! a ≡ inj₁ tt  !}) forgetRecoverLeft x) -- subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f
-- keepRecoverLeft5 {x = inj₁ x} {f = f} {a = a} = cong f (lemma ∙ sym (transportRefl a))
-- keepRecoverLeft5 {x = inj₂ y} {f = f} {a = a} = absurd (⊎-disjoint⁻ a)

--  : {x : ⊤ ⊎ B} → {f : x ≡ inj₁ tt → B} → keepLeft (recoverLeft x f) ≡ subst (λ a → a ≡ inj₁ tt → B) (sym forgetRecoverLeft) f

fromImpossibleRight : {a : ⊤ ⊎ B} → [ (λ _ → ⊤) , (λ _ → ⊥) ] a → (a ≡ inj₁ tt)
fromImpossibleRight {a = inj₁ tt} term = refl

toImpossibleRight : {a : ⊤ ⊎ B} → (a ≡ inj₁ tt) → [ (λ _ → ⊤) , (λ _ → ⊥) ] a
toImpossibleRight {a = inj₁ tt} pr = tt
toImpossibleRight {a = inj₂ b} pr = ⊎-disjoint⁻ pr

fromToImpossibleRight : {a : ⊤ ⊎ B} {p : [ (λ _ → ⊤) , (λ _ → ⊥) ] a} → toImpossibleRight {a = a} (fromImpossibleRight p) ≡ p
fromToImpossibleRight {a = inj₁ tt} = refl

-- toFromImpossibleRight : {a : ⊤ ⊎ B} {p : (a ≡ inj₁ tt)} → fromImpossibleRight (toImpossibleRight p) ≡ p
-- toFromImpossibleRight {a = inj₁ x} = lemma
-- toFromImpossibleRight {a = inj₂ y} {p = p} = absurd (⊎-disjoint⁻ p)

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

isSame : {A B : Set} → (Σ[ v ∈ (⊤ ⊎ B) ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] v → A)) ≡ (A ⊎ B)
isSame {A} {B} = isoToPath (iso go back p₁ p₂)
    where
        go : Σ[ v ∈ (⊤ ⊎ B) ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] v → A) → A ⊎ B
        go (v , gen) = recoverLeft' v gen

        back : A ⊎ B → Σ[ v ∈ (⊤ ⊎ B) ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] v → A)
        back t = (forgetLeft t) , (keepLeft' t)

        p₁ : (t : A ⊎ B) → recoverLeft' (forgetLeft t) (keepLeft' t) ≡ t
        p₁ t = recoverForgetLeft'

        p₂ : (a : Σ[ v ∈ (⊤ ⊎ B) ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] v → A)) →
            (forgetLeft (recoverLeft' (fst a) (snd a)) ,
            keepLeft' (recoverLeft' (fst a) (snd a)))
            ≡ a
        p₂ (v , gen) = ΣPathTransport→PathΣ (forgetLeft (recoverLeft' v gen) , keepLeft' (recoverLeft' v gen)) (v , gen) (thing₁ , thing₂)
            where
                thing₁ : forgetLeft (recoverLeft' v gen) ≡ v
                thing₁ = forgetRecoverLeft' {x = v} {f = gen}

                -- thing₂ : transport ((λ i → [ (λ _ → ⊤) , (λ _ → ⊥) ] (thing₁ i) → A)) (keepLeft' (recoverLeft' v gen)) ≡ gen
                -- thing₂ = ?

                thing₂ : subst (λ x → [ (λ _ → ⊤) , (λ _ → ⊥) ] x → A) (forgetRecoverLeft' {x = v} {f = gen}) (keepLeft' (recoverLeft' v gen)) ≡ gen -- transport (λ i → [ (λ _ → ⊤) , (λ _ → ⊥) ] (thing₁ i) → A) (keepLeft' (recoverLeft' v gen)) ≡ gen
                thing₂ = keepRecoverLeft''' {A = A} {B = B} {x = v} {f = gen} -- keepRecoverLeft''' -- {x = {! v  !}} {f = gen} -- keepRecoverLeft'' {B = A} {x = {! v  !}} {f = {!   !}}



-- {B : Set} (x : position p) (y : position q) (z : position r)


--     → (direction r z → Σ[ b ∈ (⊤ ⊎ B) ]
--     ( ([ (λ _ → ⊤) , (λ _ → ⊥) ] b) → direction p x))
--     ≡ (direction r z → direction p x ⊎ B)