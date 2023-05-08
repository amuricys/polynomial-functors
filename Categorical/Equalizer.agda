{-# OPTIONS --cubical #-}

module Categorical.Equalizer where

open import Categorical.Instance.SetPoly
open import Categories.Category.Instance.Sets
open import Categories.Diagram.Equalizer SetPoly
import Level
open import Categories.Diagram.Coequalizer (Sets Level.zero)
open import Data.Nat using (suc ; zero)
open import CategoryData.Everything
open import Cubical.LensEquality
open import Cubical.Foundations.Prelude
open import Data.Sum
open import Data.Product using (_×_)
open import Cubical.Data.Equality using (pathToEq ; eqToPath)
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Function
open import Cubical.HITs.SetCoequalizer
open import Relation.Binary.PropositionalEquality using () renaming (_≡_ to _≡p_)
import Cubical.HITs.SetQuotients.Properties
open import Cubical.Foundations.Transport
open SetPolynomial
open Polynomial
open SetLens
open UniversalProperty

rapaz : {p q : SetPolynomial} {f g : SetLens p q} → f ≡ g → (lens f) ≡ (lens g)
rapaz x = λ i → lens $ x i

eq : {pˢ qˢ : SetPolynomial} → (f g : SetLens pˢ qˢ) → Equalizer f g
eq pˢ@{mksetpoly  p pposSet pdirSet} qˢ@{mksetpoly  q qposSet qdirSet} f@(⇆ˢ (mpf ⇆ mdf)) g@(⇆ˢ (mpg ⇆ mdg)) = 
  record {
    obj = eqObj ;
    arr = arr ; 
    isEqualizer = isEqualizer
    }
   where -- This is the equalizer part: the set of positions of the equalizer polynomial is the equalizer set of the maps on positions
         EqualizedPosition = Σ (position p) (λ z → mpf z ≡ mpg z)
         -- And in the dependent part of the polynomial's definition here, the set of directions for each position is the SetCoequalizer
         -- of the maps on directions *partially applied* the direction from which it came. This would normally be different types, but 
         -- the positions of the equalizer have a proof that mpf posp = mpg posp, which we use to subst below.
         eqPoly : Polynomial
         eqPoly = mkpoly EqualizedPosition $ λ intele@( posp , equal ) → SetCoequalizer (mdf posp) (λ x → mdg posp (subst (λ diffPosQ → direction q diffPosQ) equal x))
         eqPosSet : isSet (position eqPoly)
         eqPosSet = isSetΣ pposSet λ x → isProp→isSet (qposSet (mpf x) (mpg x))
         eqDirSet : ∀ {po : position eqPoly} → isSet (direction eqPoly po)
         eqDirSet {posp , mapped≡} = squash
         eqObj : SetPolynomial
         eqObj = mksetpoly eqPoly eqPosSet eqDirSet
         mpe : position (poly eqObj) → position p
         mpe = fst
         mde : (fromPos : position (poly eqObj)) → direction p (mpe fromPos) → direction (poly eqObj) fromPos
         mde _ dir = inc dir
         arr : SetLens eqObj pˢ
         arr = ⇆ˢ (mpe ⇆ mde)

         mapDir≡ : ((posp , equalized) : EqualizedPosition) → {- position in E -}
                        (dir : direction q (mpg posp)) →               {- direction in Q at that position -}
            inc {A = direction q (mpf posp)}
                  {B = direction p posp}
                  {f = mdf posp}
                  {g = λ x → mdg posp (subst (λ x₁ → direction q x₁) equalized x)}
                  (mdf posp (subst (direction q) (sym equalized) dir))
            ≡
            inc (mdg posp dir)
         mapDir≡ x@(posp , equalized) dir = let
               thecoeq : inc (mdf posp (transport (λ i → direction q (equalized (~ i))) dir))
                           ≡
                     inc (mdg posp (transport (λ i → direction q (equalized i)) 
                                                   (transport (λ i → direction q (equalized (~ i)))
                                                         dir)))
               thecoeq = coeq {f = mdf posp}
                           {g = λ x → mdg posp (subst (λ y → direction q y) equalized x)}
                           (subst (direction q) (sym equalized) dir)
               AAAA : transport (λ i → direction q (equalized i)) (transport (λ i → direction q (equalized (~ i))) dir) ≡ dir
               AAAA = transport⁻Transport (sym (λ i → direction q (equalized i))) dir
               please : inc (mdg posp (transport (λ i → direction q (equalized i)) (transport (λ i → direction q (equalized (~ i))) dir))) ≡ inc (mdg posp dir)
               please = cong (inc {A = direction q (mpf posp)} {f = mdf posp} {g = λ x → mdg posp (subst (λ y → direction q y) equalized x)} ∘ mdg posp) AAAA
               in
               thecoeq ∙ please
         equal : (mpf ⇆ mdf) ∘ₚ (mpe ⇆ mde) ≡ (mpg ⇆ mdg) ∘ₚ (mpe ⇆ mde)
         equal = lensesEqual3 (funExt (λ { (_ , mapped≡) → mapped≡} )) mapDir≡

         open IsEqualizer
         isEqualizer : IsEqualizer arr f g
         equality isEqualizer = cong ⇆ˢ equal
         equalize isEqualizer {X} {h = ⇆ˢ (mph ⇆ mdh)} x = ⇆ˢ 
                           ((λ x₁ → mph x₁ , funExt⁻ (cong mapPosition $ rapaz x) x₁) 
                              ⇆ λ fromPos → inducedHom (λ x₁ y → isDirSet X x₁ y) (mdh fromPos) (lens≡→mapDir≡' (rapaz x) fromPos))
         universal isEqualizer {X} {(⇆ˢ (mph ⇆ mdh))} {eq} = cong ⇆ˢ (lensesEqual3 refl mdhproof)
           where mdhproof : (x : position (poly X)) 
                            (y : direction p (mph x)) → 
                            mdh x (transport (λ i → direction p (mph x)) y) ≡ mdh x y
                 mdhproof x y  = cong (λ a → mdh x a) obvious
                    where obvious : transport (λ i → direction p (mph x)) y ≡ y
                          obvious = transportRefl y
         unique isEqualizer {X} {(⇆ˢ (mph ⇆ mdh))} {(⇆ˢ (mpi ⇆ mdi))} {eq} eq2 = cong ⇆ˢ (lensesEqual3 mapPos≡ {!   !})
           where mapPos≡ : mpi ≡ (λ x₁ → mph x₁ , (λ i → mapPosition (lens (eq i)) x₁))
                 mapPos≡ = funExt (λ x → ΣPathP (funExt⁻ (sym (lens≡→mapPos≡ (rapaz eq2))) x , {!   !}))
      --      record { 
      --       equality = cong ⇆ˢ equal ;
            --  equalize = λ { {X} {h = ⇆ˢ (mph ⇆ mdh)} x → ⇆ˢ 
            --                ((λ x₁ → mph x₁ , funExt⁻ (cong mapPosition $ rapaz x) x₁) 
            --                   ⇆ λ fromPos → inducedHom (λ x₁ y → isDirSet X x₁ y) (mdh fromPos) (lens≡→mapDir≡' (rapaz x) fromPos) ) }  ;
      --       universal = λ {X} {(⇆ˢ (mph ⇆ mdh))} {eq2} → cong ⇆ˢ (lensesEqual3 refl λ x y → {!   !}  ); -- commutativity (isDirSet X) (\y →  mdh x {!  !}) (λ a → lens≡→mapDir≡' (cong lens eq2) x a) {!   !}) ; 
      --       unique = λ {X} {h@(⇆ˢ (mph ⇆ mdh))} {(⇆ˢ (mpi ⇆ mdi))} x → cong ⇆ˢ (lensesEqual3 (funExt λ { posX → {! mpi posX  !} }) {!   !}) 
      --       }
--            where 
                  -- universal : ∀ {X p q : SetPolynomial} {h : Lens X p}  → {!   !}
                  -- universal = λ {X} {(⇆ˢ (mph ⇆ mdh))} {eq2} → cong ⇆ˢ (lensesEqual3 refl λ x y → commutativity (isDirSet X) (\y →  mdh x {!  !}) (λ a → lens≡→mapDir≡' (cong lens eq2) x a) {!   !}) 
                  
                  
                  
import Categories.Diagram.Equalizer (Sets Level.zero) as SetsEq
eqSets : {A B : Set} → (f g : A → B) → SetsEq.Equalizer f g
eqSets {A} {B} f g = record { 
      obj = (Σ[ i ∈ A ] (f i ≡p g i)) ;
      arr = λ { (fst₁ , snd₁) → fst₁ } ; 
      isEqualizer = record { 
            equality = \{ {fst₁ , snd₁} → snd₁ }; 
            equalize = λ {X} {h} x x₁ → h x₁ , {!   !} ; 
            universal =  _≡p_.refl ; 
            unique = unique }
            }
            where unique : {eqSet : Type} → 
                           {eqArr : eqSet → A} → 
                           {eq : eqSet → Σ[ i ∈ A ] (f i ≡p g i) } → 
                           {a : {x = x₁ : eqSet} → f (eqArr x₁) ≡p g (eqArr x₁)} → 
                           (y : {x = x₁ : eqSet} → eqArr x₁ ≡p fst (eq x₁)) →
                           {x : eqSet} →
                           eq x ≡p (eqArr x , a)
                  unique {eqSet} {eqArr} {eq} {a} y {x} = let
                        anew , pro = eq x
                        res = eqArr x
                        hmm = eqToPath (a {x})
                        hmm2 = eqToPath (y {x})
                        lemma : fst (eq x) ≡ eqArr x
                        lemma = sym hmm2
                        lemma22 : eqArr x ≡ fst (eq x)
                        lemma22 = sym lemma
                        lemma2 : pathToEq {!   !} ≡ a {x}
                        lemma2 = {!   !}
                        in
                          pathToEq {!   !}

-- Coeq-rec : ∀ {ℓ} {C : Type ℓ} {A B : Set} {f g : A → B}
--       → isSet C → (h : B → C)
--       → (∀ x → h (f x) ≡ h (g x)) → SetCoequalizer f g → C
-- Coeq-rec cset h h-coeqs (inc x) = h x
-- Coeq-rec cset h h-coeqs (glue x i) = h-coeqs x i
-- Coeq-rec cset h h-coeqs (squash x y p q i j) =
--   cset (g x) (g y) (λ i → g (p i)) (λ i → g (q i)) i j
--   where g = Coeq-rec cset h h-coeqs

-- coeqSets : {A B : Set} → (f g : A → B) → Coequalizer f g
-- coeqSets {A} {B} f g = record { 
--       obj = SetCoequalizer f g ; 
--       arr = λ x → inc x; 
--       isCoequalizer = record { 
--             equality = \{x} → pathToEq (coeq x) ; 
--             coequalize = λ { {_} {h} x (inc x₁) → h x₁
--                            ; {_} {h} x (coeq a i) → (eqToPath (x {a})) i
--                            ; {_} {h} x (squash x₁ x₂ p q i i₃) → {! eqToPath x !} }; 
--             universal = {!   !} ; 
--             unique = {!   !} 
--             }
--       }
--   where coequalize : {coeqSetCandidate : Set} →
--                      {h : B → coeqSetCandidate} →
--                      (x : {x = x₂ : A} → h (f x₂) ≡p h (g x₂)) →
--                      (coeqSetElmt : SetCoequalizer f g) → 
--                      coeqSetCandidate
--         coequalize {coeqSetCandidate} {h} x (inc x₁) = h x₁
--         coequalize {coeqSetCandidate} {h} x (coeq x₁ i) = eqToPath (x {x₁}) i
--         coequalize {coeqSetCandidate} {h} x (squash coeqSetElmt coeqSetElmt₁ x₁ y i i₃) = {!  !}


-- (Σ[ i ∈ p.position ] (p.direction i → q.position))
-- p'(1) := {i ∈ p(1) | mpf(i) = mpg(i)}
                    