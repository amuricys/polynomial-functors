{-# OPTIONS --cubical #-}

module Categorical.Exponential where

open import Categorical.CubicalPoly
import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Common.CategoryData
open import Cubical.Data.Sigma
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Bool
open import Data.Unit
open import Data.Empty
open import Categorical.Product
open import Categories.Object.Product Poly
import Categories.Category.CartesianClosed.Canonical as Canonical
open import Function using (_∘_ ; _$_)

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = MkPolynomial ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))
open import Cubical.PolynomialEquals
open import Cubical.Foundations.Prelude
open Polynomial
-- Exercise 4.29
p^0≡1 : {p : Polynomial} → p ^ Zero ≡ One
p^0≡1 {p} = poly≡∀' pos≡ dir≡
  where
    lemma : {A : ⊥ → Type} → ((i : ⊥) → A i) ≡ ⊤
    lemma = isoToPath (iso (λ x → tt) (λ {x ()}) (λ {tt → refl}) λ {a i ()})

    pos≡ : position (p ^ Zero) ≡ position One
    pos≡ =  lemma

    lemmaDir : {A : ⊥ → Type} → Σ ⊥ A ≡ ⊥
    lemmaDir = isoToPath (iso fst (λ {()}) (λ {()}) λ {()})

    dir≡ : (pos : position (p ^ Zero)) → direction (p ^ Zero) pos ≡ subst (λ x → x → Type) (sym pos≡) (direction One) pos
    dir≡ pos = lemmaDir

open import Cubical.Core.Primitives
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function hiding (_∘_)
open import Cubical.Foundations.HLevels

p^1≡p : {p : Polynomial} → p ^ One ≡ p
p^1≡p {p@(MkPolynomial pos dir)} = poly≡ pos≡ dir≡
  where
      lemma₁ : {A : Type} → (⊤ → A) ≡ A
      lemma₁ = isoToPath (iso (λ x → x tt) (λ A tt → A) (λ b → refl) λ i → refl)

      lemma₄ : {A : Type} → (A → ⊤) ≡ ⊤
      lemma₄ = isoToPath (iso (λ x → tt) (λ x x₁ → tt) (λ b → refl) λ a → refl)
      
      lemma₃ : (⊤ ⊎ ⊥) ≡ ⊤
      lemma₃ = isoToPath (iso (λ x → tt) (λ x → inj₁ tt) (λ b → refl) λ {(inj₁ a) → refl ; (inj₂ ()) })

      lemma₂ : {A : Type} → (A → ⊤ ⊎ ⊥) ≡ ⊤
      lemma₂ {A} = (cong (λ x → (A → x)) lemma₃) ∙ lemma₄

      lemma₅ : {A : Type} → (Σ[ a ∈ A ] ⊤) ≡ A
      lemma₅ = isoToPath (iso fst (λ x → x , tt) (λ b → refl) λ a → refl)

      lemma : ((index : ⊤) → Σ pos (λ i → dir i → ⊤ ⊎ ⊥)) ≡ pos
      lemma = lemma₁ ∙ cong (λ a → Σ pos a) help ∙ lemma₅
        where
          help : (λ (pos : pos) → dir pos → ⊤ ⊎ ⊥) ≡ (λ (a : pos) → ⊤)
          help = funExt (λ x → lemma₂)

      pos≡ : position (p ^ One) ≡ position p
      pos≡ = lemma

      dir≡ : (subst (λ x → x → Type) pos≡ (direction (p ^ One))) ≡ direction p
      dir≡ = funExt (λ {x → {! refl   !}})

data ThreeSet : Set where
  three1 three2 three3 : ThreeSet

data TwoSet : Set where
  two1 two2 : TwoSet

data NineSet : Set where
  nine1 nine2 nine3 nine4 nine5 nine6 nine7 nine8 nine9 : NineSet

Three : Polynomial
Three = MkPolynomial ThreeSet λ x → ⊥

Two : Polynomial
Two = MkPolynomial TwoSet (λ x → ⊥)

Nine : Polynomial
Nine = MkPolynomial NineSet (λ x → ⊥)

open import Cubical.Data.Equality

3^2≡9 : Three ^ Two ≡ Nine
3^2≡9 = poly≡∀' pos≡ dir≡
  where other : ((index : TwoSet) → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)) ≡ NineSet
        other = isoToPath (iso go back proofSection proofRetract)
                where go : (TwoSet → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)) → NineSet
                      go two with ( two two1 , two two2 )
                      ... | (three1 , snd₁) , three1 , snd₂ = nine1
                      ... | (three1 , snd₁) , three2 , snd₂ = nine2
                      ... | (three1 , snd₁) , three3 , snd₂ = nine3
                      ... | (three2 , snd₁) , three1 , snd₂ = nine4
                      ... | (three2 , snd₁) , three2 , snd₂ = nine5
                      ... | (three2 , snd₁) , three3 , snd₂ = nine6
                      ... | (three3 , snd₁) , three1 , snd₂ = nine7
                      ... | (three3 , snd₁) , three2 , snd₂ = nine8
                      ... | (three3 , snd₁) , three3 , snd₂ = nine9
                      back : NineSet → TwoSet → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)
                      back nine1 two1 = three1 , λ ()
                      back nine1 two2 = three1 , (λ ())
                      back nine2 two1 = three1 , (λ ())
                      back nine2 two2 = three2 , (λ ())
                      back nine3 two1 = three1 , (λ ())
                      back nine3 two2 = three3 , (λ ())
                      back nine4 two1 = three2 , (λ ())
                      back nine4 two2 = three1 , (λ ())
                      back nine5 two1 = three2 , (λ ())
                      back nine5 two2 = three2 , (λ ())
                      back nine6 two1 = three2 , (λ ())
                      back nine6 two2 = three3 , (λ ())
                      back nine7 two1 = three3 , (λ ())
                      back nine7 two2 = three1 , (λ ())
                      back nine8 two1 = three3 , (λ ())
                      back nine8 two2 = three2 , (λ ())
                      back nine9 two1 = three3 , (λ ())
                      back nine9 two2 = three3 , (λ ())
                      proofSection : (b : NineSet) → go (back b) ≡ b
                      proofSection nine1 = refl
                      proofSection nine2 = refl
                      proofSection nine3 = refl
                      proofSection nine4 = refl
                      proofSection nine5 = refl
                      proofSection nine6 = refl
                      proofSection nine7 = refl
                      proofSection nine8 = refl
                      proofSection nine9 = refl
                      helper :  ∀ {X Y} {some : ⊥ → ⊤ ⊎ ⊥} → X ≡p (Y , some) → X ≡p (Y , (λ ()))
                      helper {X} {Y} one = ctop (ptoc one ∙ cong (λ a → Y , a) functionFromFalse)
                        where functionFromFalse : {some : ⊥ → ⊤ ⊎ ⊥} → some ≡ λ ()
                              functionFromFalse = funExt (λ ())
                      proofRetract : (a : TwoSet → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)) → back (go a) ≡ a
                      proofRetract a with a two1 | a two2 | (Eq.inspect a two1) | (Eq.inspect a two2)
                      ... | (three1 , snd₁) | (three1 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
                      ... | (three1 , snd₁) | (three2 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
                      ... | (three1 , snd₁) | (three3 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
                      ... | (three2 , snd₁) | (three1 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
                      ... | (three2 , snd₁) | (three2 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
                      ... | (three2 , snd₁) | (three3 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
                      ... | (three3 , snd₁) | (three1 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
                      ... | (three3 , snd₁) | (three2 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
                      ... | (three3 , snd₁) | (three3 , snd₂) | Eq.[ eq₁ ] | Eq.[ eq₂ ] = funExt λ {two1 → sym ∘ ptoc ∘ helper $ eq₁; two2 → sym ∘ ptoc ∘ helper $ eq₂}
        pos≡ : position (Three ^ Two) ≡ position Nine
        pos≡ = other
        dir≡ : (posA : (index : TwoSet) → Σ ThreeSet (λ i → ⊥ → ⊤ ⊎ ⊥)) →
            Σ TwoSet
            (λ index →
              Σ ⊥ (λ a → [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posA index) a)))
            ≡c ⊥
        dir≡ p = isoToPath (iso (λ { () }) (λ ()) (λ ()) λ { () i })

rtoq : (r : Polynomial) -> (q : Polynomial) -> Polynomial
rtoq r (MkPolynomial posQ dirQ) = depProd (posQ , λ j → r ◂ (Y + Constant (dirQ j)))

ev : {A B : Polynomial} -> Arrow (rtoq B A * A) B
ev {A} {B} = mp ⇄ md
    where mp : position (rtoq B A * A) → position B
          mp (posB^A , posA) = fst (posB^A posA)
          md : (fromPos : position (rtoq B A * A)) → direction B (mp fromPos) → direction (rtoq B A * A) fromPos
          md (posB^A , posA) x with (snd (posB^A posA)) x in eq
          ... | inj₂ v = inj₂ v
          ... | inj₁ s = inj₁ (posA , x , help eq)
                where help : (snd (posB^A posA) x) Eq.≡ inj₁ s -> [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posB^A posA) x)
                      help p rewrite p = tt

λg : {X A B : Polynomial} -> (X×A : Product X A) → Arrow (Product.A×B X×A) B → Arrow X (rtoq B A)  
λg {X} {A} {B} record { A×B = A×B ; π₁ = π₁ ; π₂ = π₂ ; ⟨_,_⟩ = ⟨_,_⟩ ; project₁ = project₁ ; project₂ = project₂ ; unique = unique } (mp ⇄ md) = let
  emp ⇄ emd = ev {A} {B}
  -- MkPolynomial h m = Product.A×B p
  -- hmm : position X -> position A -> position (X * A)
  -- hmm posX posA = posX , posA
  -- hmmm : position (X * A) -> position (Product.A×B (prod {X} {A}))
  -- hmmm p = p
  help : position A×B
  help = {!  !}
  in
  (\ x i → mp help , {!   !}) ⇄ {!   !} 

exp : {A B : Polynomial} -> Exponential A B
exp {A} {B} = record
    { B^A = rtoq B A
    ; product = prod
    ; eval = ev
    ; λg = \{X} X×A x → {!   !}
    ; β = {!   !}
    ; λ-unique = {!   !}
    }
      