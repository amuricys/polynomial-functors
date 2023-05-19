{-# OPTIONS --cubical --allow-unsolved-metas #-}

module Categorical.Poly.Monoidal.CompositionProduct where

open import CategoryData.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Agda.Builtin.Unit
open import Cubical.PolynomialEquals
open import Cubical.Proofs
open import Categories.Category.Monoidal
open import Categorical.Poly.Instance
open import Categories.Functor.Bifunctor
open import Categories.Functor
open import Cubical.LensEquality
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Transport
open import Function
open Polynomial

leftUnit : {p : Polynomial} → Y ◂ p ≡ p
leftUnit {p} = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Type} → Σ ⊤ (λ i → ⊤ → A) ≡ A
        lemma = isoToPath (iso (λ x → snd x tt) (λ x → tt , (λ _ → x)) (λ b → refl) λ a → refl)

        pos≡ : position (Y ◂ p) ≡ position p
        pos≡ = lemma

        lemmaDir : {f : ⊤ → Set} → Σ ⊤ f ≡ f tt
        lemmaDir = isoToPath (iso (λ {(tt , hmm) → hmm}) (λ x → tt , x) (λ b → refl) λ a → refl)

        dir≡ : (posA : position (Y ◂ p)) → direction (Y ◂ p) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ (tt , hmm) = lemmaDir ∙ cong (direction p) (sym (transportRefl (hmm tt)))

rightUnit : {p : Polynomial} → p ◂ Y ≡ p
rightUnit {p} = poly≡∀' pos≡ dir≡
    where
        lemma : {A : Type} {B : A → Type} → Σ A (λ i → B i → ⊤) ≡ A
        lemma = isoToPath (iso fst (λ x → x , λ x₁ → tt) (λ b → refl) λ a → refl)

        pos≡ : position (p ◂ Y) ≡ position p
        pos≡ = lemma

        lemmaDir : {A : Type} → Σ A (λ _ → ⊤) ≡ A
        lemmaDir = isoToPath (iso fst (λ x → x , tt) (λ b → refl) λ a → refl)

        dir≡ : (posA : position (p ◂ Y)) → direction (p ◂ Y) posA ≡ subst (λ x → x → Type) (sym pos≡) (direction p) posA
        dir≡ posA = lemmaDir ∙ cong (direction p) (sym (transportRefl (fst posA)))


-- transportRefl : (x : A) → transport refl x ≡ x
-- transportRefl {A = A} x i = transp (λ _ → A) i x

open import Data.String
open import Data.Nat
someFn : String → ℕ
someFn _ = zero

halp : {p : Polynomial} {posp : position p} {dirp : direction p posp} → dirp ≡
    transport (λ j → direction p (transp (λ i → position p) j posp))
    (transport
       (λ i → direction p (transp (λ _ → position p) (~ i) posp))
       dirp)
halp {p} {posp} {dirp} = sym (aa {B = direction p} ∙ bbb ∙ ccc)
  where 
        lemma : {j : I} → transp (λ i → position p) j posp ≡ posp
        lemma {j} i = transp (λ _ → position p) (i ∨ j) posp
        lemma2 : ∀ {a} → transport (λ j → direction p posp) a ≡ a
        lemma2 {a} = transportRefl a  
        aa : {A : Set} {a : A} {B : A → Set} {b : B a} →
             transport
             (λ j → B (transp (λ _ → A) j a))
             (transport
              (sym (λ i → B (transp (λ _ → A) i a))) b)
             ≡
             transport
             (λ _ → B a)
             (transport
             (λ _ → B a) b)            
        -- direction p (transp (λ i₃ → position p) i1 posp)
        aa {A} {a} {B} {b} i = transport (λ j → B (transp (λ _ → A) (i ∨ j) a)) (transport (λ j → B (transp (λ _ → A) (i ∨ ~ j) a)) b)
        bbb : transport (λ j → direction p posp) (transport (λ i → direction p posp) dirp) ≡ transport (λ i → direction p posp) dirp
        bbb = transportRefl (transport (λ i → direction p posp) dirp)
        ccc : (transport (λ i → direction p posp) dirp) ≡ dirp
        ccc = transportRefl dirp



  -- lemma pr x y i =
  -- transp (λ j → direction p (transp (λ _ → position p) (j ∨ i) x))
  --        i
  --        (mapDirection f (transp (λ _ → position p) i x)
  --                        (transp (λ j → direction q (pr (~ j) (transp (λ _ → position p) (~ j ∨ i) x)))
  --                                i0
  --                                y))



-- snd (snd gm dirp) dirq ≡
--       transp (λ i → position r) i0
--       (snd
--        (snd gm
--         (transp (λ j → direction p (transp (λ i → position p) j (fst gm)))
--          i0
--          (transp
--           (λ i → direction p (transp (λ _ → position p) (~ i) (fst gm))) i0
--           dirp)))
--        (transp
--         (λ j →
--            direction q
--            (transp (λ i → position q) j
--             (fst
--              (snd gm
--               (transp
--                (λ j₁ → direction p (transp (λ i → position p) j₁ (fst gm))) i0
--                (transp
--                 (λ i → direction p (transp (λ _ → position p) (~ i) (fst gm))) i0
--                 dirp))))))
--         i0
--         (transp
--          (λ i →
--             direction q
--             (transp (λ _ → position q) (~ i)
--              (fst
--               (snd gm
--                (transp (λ j → direction p (transp (λ i₃ → position p) j (fst gm)))
--                 i0
--                 (transp
--                  (λ i₃ → direction p (transp (λ _ → position p) (~ i₃) (fst gm))) i0
--                  dirp))))))
--          i0
--          (transp
--           (λ i →
--              direction q
--              (fst
--               (snd gm
--                (hcomp
--                 (doubleComp-faces
--                  (λ _ →
--                     transp (λ i₃ → direction p (transp (λ _ → position p) i₃ (fst gm)))
--                     i0
--                     (transp
--                      (λ i₃ → direction p (transp (λ _ → position p) (~ i₃) (fst gm))) i0
--                      dirp))
--                  (λ i₃ →
--                     hcomp
--                     (doubleComp-faces
--                      (λ _ →
--                         transp (λ i₄ → direction p (fst gm)) i0
--                         (transp (λ i₄ → direction p (fst gm)) i0 dirp))
--                      (λ i₄ → transp (λ _ → direction p (fst gm)) i₄ dirp) i₃)
--                     (transp (λ _ → direction p (fst gm)) i₃
--                      (transp (λ i₄ → direction p (fst gm)) i0 dirp)))
--                  (~ i))
--                 (transp
--                  (λ i₃ →
--                     direction p (transp (λ _ → position p) (~ i ∨ i₃) (fst gm)))
--                  i0
--                  (transp
--                   (λ i₃ →
--                      direction p (transp (λ _ → position p) (~ i ∨ ~ i₃) (fst gm)))
--                   i0 dirp))))))
--           i0 dirq))))

open import CategoryData.Composition
assoc : {p q r : Polynomial} → (p ◂ q) ◂ r ≡ p ◂ (q ◂ r)
assoc {p} {q} {r} = poly≡∀ pos≡ dir≡
    where pos≡norm : Σ (Σ (position p) (λ i → direction p i → position q))
                       (λ i →
                           Σ (direction p (fst i)) (λ a → direction q (snd i a)) → position r)
                    ≡
                    Σ (position p)
                      (λ i →
                          direction p i →
                          Σ (position q) (λ i₃ → direction q i₃ → position r))
          pos≡norm = isoToPath (iso go back (λ _ → refl) λ _ → refl)
            where go :  Σ (Σ (position p) (λ i → direction p i → position q))
                          (λ i → Σ (direction p (fst i)) (λ a → direction q (snd i a))
                                 → position r)
                        →
                        Σ (position p)
                          (λ i →
                              direction p i →
                              Σ (position q) (λ i₃ → direction q i₃ → position r))
                  go ((posp , dirptoposq) , fromdirandfunctoposr) = 
                    posp , (λ dirp → (dirptoposq dirp) , (λ dirqatthatpos → fromdirandfunctoposr (dirp , dirqatthatpos)))
                  back : Σ (position p)
                          (λ i →
                              direction p i →
                              Σ (position q) (λ i₃ → direction q i₃ → position r)) 
                        → 
                        Σ (Σ (position p) (λ i → direction p i → position q))
                          (λ i → Σ (direction p (fst i)) (λ a → direction q (snd i a))
                                 → position r)
                  back (posp , postodir) = 
                    (posp , (λ dirp → fst (postodir dirp))) , λ { (dirp , dirq) → snd (postodir dirp) dirq }
                        
          pos≡ : position (p ◂ q ◂ r) ≡ position (p ◂ (q ◂ r))
          pos≡ = pos≡norm
          dir≡ : (posB : Σ (position p) (λ i → direction p i → position (q ◂ r))) →
                    subst (λ x → x → Type) pos≡ (dir (p ◂ q) r) posB 
                  ≡
                 dir p (q ◂ r) posB
          dir≡ gm = isoToPath (iso (λ { ((dirp , dirq) , dirr) →  subst (direction p) (transportRefl (fst gm)) dirp , subst (direction q) (transportRefl (fst (snd gm  (transp (λ j → direction p (transp (λ i → position p) j (fst gm))) i0 dirp)))) dirq , subst (direction r) (transportRefl ((snd
                                      (snd gm
                                        (transp (λ j → direction p (transp (λ i → position p) j (fst gm)))
                                        i0 dirp))
                                      (transp
                                        (λ j →
                                          direction q
                                          (transp (λ i → position q) j
                                            (fst
                                            (snd gm
                                              (transp
                                              (λ j₁ → direction p (transp (λ i → position p) j₁ (fst gm))) i0
                                              dirp)))))
                                        i0 dirq)))) dirr })
                                   (λ { (dirp , dirq , dirr)   → (subst (direction p) (sym (transportRefl (fst gm))) dirp , subst (direction q) (sym ((transportRefl (fst (snd gm  (transp (λ j → direction p (transp (λ i → position p) j (fst gm))) i0 (subst (direction p) (sym (transportRefl (fst gm))) dirp))))))) (subst (λ diff → direction q (fst (snd gm diff)) ) (halp {p}) dirq)) , 
                                              subst (direction r) (sym {!   !}) dirr }) 
                                   {!   !}
                                   {!   !})

open Functor
open import Function
bifunctor : Bifunctor Poly Poly Poly
F₀ bifunctor (p , q) = p ◂ q
F₁ bifunctor ((mpf ⇆ mdf) , (mpg ⇆ mdg)) = (λ { (a , b) → mpf a , λ { x → mpg (b (mdf a x)) } }) ⇆ λ { (x , y) (w , z) → (mdf x w) , (mdg (y (mdf x w)) z) }
identity bifunctor = refl
homomorphism bifunctor = refl
F-resp-≈ bifunctor {p , r} {q , s} {(fpq ⇆ fpq♯) , (frs ⇆ frs♯)} {(gpq ⇆ gpq♯) , (grs ⇆ grs♯)} (fst≡ , snd≡) 
  = lensesEqual3 pos≡ {!   !}
     where pqPosEq : fpq ≡ gpq
           pqPosEq = lens≡→mapPos≡ fst≡
           pos≡ : (λ { (a , b) → fpq a , (λ { x → frs (b (fpq♯ a x)) }) }) ≡ (λ { (a , b) → gpq a , (λ { x → grs (b (gpq♯ a x)) }) })
           iwant : (x : pos p r) → (λ { (a , b) → fpq a , (λ { x → frs (b (fpq♯ a x)) }) }) x ≡ (λ { (a , b) → gpq a , (λ { x → grs (b (gpq♯ a x)) }) }) x
           iwant (posp , fromdirqtoposr ) = 
             ΣPathP $ funExt⁻ pqPosEq posp , toPathP t
               where t : transport
                         (λ i → direction q (funExt⁻ pqPosEq posp i) → position s)
                         (λ { x → frs (fromdirqtoposr (fpq♯ posp x)) })
                         ≡ (λ { x → grs (fromdirqtoposr (gpq♯ posp x)) })
                     t i = transp (λ j → transport (λ i₃ → {!  !}) (λ { x → frs (fromdirqtoposr (fpq♯ posp x)) })) {!   !} {!   !}
           pos≡ = funExt iwant

monoidal : Monoidal Poly
monoidal = record
    { ⊗ = bifunctor
    ; unit = Y
    ; unitorˡ = record { 
        from = (λ { (tt , y) → y tt }) ⇆ λ { (tt , y) z → tt , z } ; 
        to = (λ { x → tt , λ _ → x }) ⇆ λ { fromPos → snd } ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; unitorʳ = record { 
        from = fst ⇆ λ { _ x → x , tt } ; 
        to = (λ x → x , (λ _ → tt)) ⇆ λ _ → fst ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; associator = record { 
        from = (λ { ((x , z) , y) → x , (λ x → z x , (λ x₁ → y (x , x₁))) }) ⇆ λ { ((_ , hmm) , bbb) (fst₂ , (what , is)) → (fst₂ , what) , is } ; 
        to = (λ { (a , b) → (a , (λ x → fst (b x))) , λ { (idk , wat) → snd (b idk) wat } }) ⇆ λ { (x , y) ((jee , idkk) , w) → jee , idkk , w } ; 
        iso = record { isoˡ = refl ; isoʳ = refl } 
        }
    ; unitorˡ-commute-from = refl
    ; unitorˡ-commute-to = refl
    ; unitorʳ-commute-from = refl
    ; unitorʳ-commute-to = refl
    ; assoc-commute-from = refl
    ; assoc-commute-to = refl
    ; triangle = refl
    ; pentagon = refl
    }
 