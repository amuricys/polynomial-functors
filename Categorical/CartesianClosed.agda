{-# OPTIONS --cubical #-}

module Categorical.CartesianClosed where

open import CategoryData.Everything
open import Categorical.Instance.Poly

import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Sigma.Properties -- hiding (_×_)
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (Σ-syntax ; curry ; uncurry)
open import Categorical.Product
open import Categories.Object.Product Poly
open import Categorical.Terminal
open import Cubical.Proofs
open import Cubical.LensEquality
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
import Categories.Category.CartesianClosed.Canonical Poly as Canonical
open import Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Utils.CoproductUtils hiding (lemma)

open Polynomial

eval : {p q : Polynomial} → Lens ((q ^ p) * p) q
eval {p} {q} = mapPos ⇆ mapDir
    where
        mapPos : position ((q ^ p) * p) → position q
        mapPos (posQ^P , posP) = fst (posQ^P posP)

        mapDir : (pos : position ((q ^ p) * p))
            → direction q (mapPos pos) 
            → direction ((q ^ p) * p) pos
        mapDir (posQ^P , posP) dir with (snd (posQ^P posP)) dir in eq
        ... | inj₂ y = inj₂ y
        ... | inj₁ x = inj₁ (posP , dir , help)
            where
                help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posQ^P posP) dir)
                help rewrite eq = tt
eraseLeft : {A B : Set} → A ⊎ B → ⊤ ⊎ B
eraseLeft f = [ (λ _ → inj₁ tt) , inj₂ ] f
curry : {p q r : Polynomial} → Lens (p * q) r → Lens p (r ^ q)
curry {p} {q} {r} (f ⇆ f♯) = mapPos ⇆ mapDir
    where


        mapPos : position p → position (r ^ q)
        mapPos posP posQ = f (posP , posQ) , λ {dirR → eraseLeft  (f♯ (posP , posQ) dirR)}

        mapDir : (pos : position p) → direction (r ^ q) (mapPos pos) → direction p pos
        mapDir posP (posQ , dirR , g) with f♯ (posP , posQ) dirR
        ... | inj₁ x = x

uncurry : {p q r : Polynomial} → Lens p (q ^ r) → Lens (p * r) q
uncurry {p} {q} {r} (f ⇆ f♯) = mapPos ⇆ mapDir
    where
        mapPos : position (p * r) → position q
        mapPos (posP , posR) = fst (f posP posR)

        mapDir : (pos : position (p * r)) → direction q (mapPos pos) → direction (p * r) pos
        mapDir (posP , posR) dirQ with snd (f posP posR) dirQ in eq
        ... | inj₂ y = inj₂ y
        ... | inj₁ x = inj₁ (f♯ posP (posR , dirQ , help))
            where
                help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (f posP posR) dirQ)
                help rewrite eq = tt

mpEv : {A B : Polynomial} → position (B ^ A * A) → position B
mpEv (posB^A , posA) = fst (posB^A posA)
mdEv : {A B : Polynomial} → (fromPos : position (B ^ A * A)) → direction B (mpEv fromPos) → direction (B ^ A * A) fromPos
mdEv (posB^A , posA) x with (snd (posB^A posA)) x in eq
... | inj₂ v = inj₂ v
... | inj₁ s = inj₁ (posA , x , help eq)
        where help : (snd (posB^A posA) x) Eq.≡ inj₁ s → [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (posB^A posA) x)
              help p rewrite p = tt
ev : {A B : Polynomial} → Lens (B ^ A * A) B
ev {A} {B} = mpEv ⇆ mdEv

-- For the first application of [_,_] to exist, ab has to be inj₁
convGeneral : {A B : Set} (ab : A ⊎ B) → [ (λ _ → ⊤) , (λ _ → ⊥) ] ( [_,_] {C =  const (⊤ ⊎ B) } (λ _ → inj₁ tt) inj₂ ab ) → A
convGeneral (inj₁ x) pr = x

convGeneral' : {A B : Set} (ab : A ⊎ B) → [ (λ _ → ⊤) , (λ _ → ⊥) ] ab → A
convGeneral' (inj₁ x) pr = x

univPropCoproduct : {p q : Polynomial} → Lens p q ≡ ((i : position p) → Lens (purePower (direction p i)) q)
univPropCoproduct {p} {q} = isoToPath (iso go 
                                           back
                                           (λ b → refl)
                                           λ a → refl)
      where go : Lens p q → (i : position p) → Lens (purePower (direction p i)) q
            go (f ⇆ f♯) = λ i → (const (f i)) ⇆ const (f♯ i)
            back : ((i : position p) → Lens (purePower (direction p i)) q) → Lens p q
            back pit = ( (λ y → mapPosition y tt) ∘  pit) ⇆ ((λ y → mapDirection y tt) ∘ pit)

-- the arrow from 1 hack is to get around size issues, polys are bigger than sets
applyingIsSameAsComposingWithConstant : {r : Polynomial} → {A : Set} → Lens 𝟙 (r ◂ (Constant A)) ≡ r ⦅ A ⦆
applyingIsSameAsComposingWithConstant {r} {A} = isoToPath (iso go
                                                               back
                                                               (λ b → refl)
                                                               λ a → lensesEqual3 refl λ x () )
      where go : Lens 𝟙 (r ◂ (Constant A)) → r ⦅ A ⦆
            go (f ⇆ f♯) = f tt
            back : r ⦅ A ⦆ → Lens 𝟙 (r ◂ (Constant A))
            back (pos , md) = (λ _ → pos , md) ⇆ λ { fromPos () }

univPropProduct : {p q : Polynomial} {qi : position q → Polynomial} → Lens p (ΠPoly (position q , qi)) ≡ ((i : position q) → Lens p (qi i))
univPropProduct {p} {q} {qi} = universalPropertyProduct

univPropProdCoprod : {p q r : Polynomial} → Lens p (r ^ q) ≡ ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ◂ (Y + Constant (direction q j))))
univPropProdCoprod {p} {q} {r} = substed
   where substed : Lens p (r ^ q) ≡ ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ◂ (Y + Constant (direction q j))))
         substed = univPropCoproduct ∙ substed2
            where lemma : ∀ {a b : position p → Type} → a ≡ b → ((i : position p) → a i) ≡ ((i : position p) → b i)
                  lemma pr = cong (λ a₁ → (i : position p) → a₁ i) pr
                  substed2 : ((i : position p) → Lens (purePower (direction p i)) (r ^ q))
                                ≡
                             ((i : position p) (j : position q) → Lens (purePower (direction p i)) (r ◂ Y + Constant (direction q j)))
                  substed2 = lemma (funExt λ x → univPropProduct {q = q})

yoneda : {q : Polynomial} {i : Set} → Lens (purePower i) q ≡ q ⦅ i ⦆
yoneda {q} {i} = isoToPath (iso go
                                back
                                (λ b → refl) 
                                λ a → refl)
      where go : Lens (purePower (i)) q → q ⦅ i ⦆
            go (f ⇆ f♯) = (f tt) , (f♯ tt)
            back : q ⦅ i ⦆ → Lens (purePower (i)) q
            back (posq , mapdir) = const posq ⇆ λ fromPos x → mapdir x

lemmalemma : {p q : Polynomial} → {a b : position p → position q → Set} → a ≡ b → ((i : position p) (j : position q) → a i j) ≡ ((i : position p) (j : position q) → b i j)
lemmalemma {p} {q} pr = cong (λ a₁ → (i : position p) (j : position q) → a₁ i j) pr

useYon : {p q r : Polynomial} → ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ◂ (Y + Constant (direction q j)))) ≡ ((i : position p) → (j : position q) → (r ◂ (Y + Constant (direction q j))) ⦅ direction p i ⦆ )
useYon {p} {q} {r} = lemmalemma {p} {q} (funExt λ x → funExt λ x₁ → yoneda)

-- wrong : {p q r : Polynomial} → ((i : position p) → (j : position q) → (r ◂ (Y + Constant (direction q j))) ⦅ direction p i ⦆ ) ≡ ((i : position p) → (j : position q) → (r ⦅ direction q j  ⊎ direction p i ⦆ ))
-- wrong {p} {q} {r} = isoToPath (iso go 
--                                    {!   !}
--                                    {!   !}
--                                    {!   !})
--   where go : ((i : position p) (j : position q) → (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆) → (i : position p) (j : position q) → r ⦅ direction q j ⊎ direction p i ⦆
--         go exx = λ i j → (fst $ fst (exx i j)) , λ { x → (λ { y → {! y  !} }) ∘ snd $ exx i j }
--         back : ((i : position p) (j : position q) → r ⦅ direction q j ⊎ direction p i ⦆) → (i : position p) (j : position q) → (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆
--         back exxx = {!   !}

three : {p q r : Polynomial} → ((i : position p) → (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆) ≡ ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j)))
three {p} {q} {r} = isoToPath (iso (λ x i j → (fst $ x i j) , (λ x₁ → snd (x i j) x₁)) 
                                 (λ x i j → x i j) 
                                 (λ b → refl) 
                                 λ a → refl)


---------------- Clean attempt

variable
    p q r : Polynomial

groupPi : {A B : Type} {C : A → B → Type}
    → ((a : A) (b : B) → C a b) 
    ≡ ((a×b : (A × B)) → C (fst a×b) (snd a×b))
groupPi = isoToPath (iso (λ f → λ {(a , b) → f a b}) (λ f a b → f (a , b)) (λ b → refl) λ a → refl)

π≡ : {I : Type} {B C : I → Type} → B ≡ C → ((i : I) → B i) ≡ ((i : I) → C i)
π≡ {I} p = cong (λ h → (i : I) → h i) p

-- Proposition 2.54, page 32
prop254 : Lens p q ≡ ((i : position p) → Σ[ j ∈ position q ] (direction q j → direction p i))
prop254 = isoToPath (iso go back (λ b → refl) λ b → refl)
    where
        go : Lens p q → (i : position p) → Σ[ j ∈ position q ] (direction q j → direction p i)
        go (f ⇆ f♯) posP =  f posP , f♯ posP

        back : ((i : position p) → Σ[ j ∈ position q ] (direction q j → direction p i)) → Lens p q
        back f = (λ posP → fst (f posP)) ⇆ λ posP → snd (f posP)


-- By definition of exponential object. 4.27
zero' : Lens p (r ^ q)
     ≡ Lens p (ΠPoly (position q , λ j → r ◂ Y + Constant (direction q j)))
zero' = refl

-- By universal property of products and coproducts.  
one' : Lens p (ΠPoly (position q , λ j → r ◂ Y + Constant (direction q j)))
     ≡ ((i : position p) (j : position q) → Lens (purePower (direction p i)) (r ◂ Y + Constant (direction q j)))
one' = univPropProdCoprod

-- By yoneda lemma.
two' : ((i : position p) (j : position q) → Lens (purePower (direction p i)) (r ◂ Y + Constant (direction q j)))
     ≡ ((i : position p) (j : position q) → (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆)
two' = π≡ (funExt (λ posP → π≡ (funExt (λ posQ → yoneda))))

-- UNSURE IF THE TYPE SHOULD BE (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆ 

-- Should be possible to fill holes.
three' : ((i : position p) (j : position q) → (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆)
       ≡ ((i : position p) (j : position q) → Σ[ k ∈ position r ] ((direction r k) → (direction p i) ⊎ (direction q j)))
three' {p} {q} {r} = π≡ (funExt λ posP → π≡ (funExt λ posQ → isoToPath (iso (go posP posQ) (back posP posQ) (λ b → ΣPathP (refl , funExt (λ dir → pr))) λ a → backProof posP posQ a )))
    where
        go : (posP : position p) (posQ : position q) → (r ◂ Y + Constant (direction q posQ)) ⦅ direction p posP ⦆ → Σ-syntax (position r) (λ k → direction r k → direction p posP ⊎ direction q posQ)
        go posP posQ ((posR , snd₂) , snd₁) = posR  , λ dir → recoverLeft (snd₂ dir) λ pr → snd₁ (dir , toImpossibleRight pr)

        back : (posP : position p) (posQ : position q) → Σ-syntax (position r) (λ k → direction r k → direction p posP ⊎ direction q posQ) → (r ◂ Y + Constant (direction q posQ)) ⦅ direction p posP ⦆
        back posP posQ (posR , f) = (posR , λ x → forgetLeft (f x)) , λ {(dir , snd₁) → keepLeft (f dir) (fromImpossibleRight snd₁)  }

        pr : {A B : Type} {x : A ⊎ B} → recoverLeft (forgetLeft x)
            (λ pr →
                keepLeft x (fromImpossibleRight (toImpossibleRight pr)))
            ≡ x
        pr {A} {B} {x} = cong (recoverLeft (forgetLeft x)) (funExt (λ y → cong (keepLeft x) toFromImpossibleRight)) ∙ recoverForgetLeft

        backProof : (posP : position p) (posQ : position q) (a : (r ◂ Y + Constant (direction q posQ)) ⦅ direction p posP ⦆) → back posP posQ (go posP posQ a) ≡ a
        backProof posP posQ ((posR , f) , g) =  ΣPathP (ΣPathP (refl , funExt (λ x → forgetRecoverLeft2 (f x) λ y → g (x , toImpossibleRight y)  )) ,  (toPathP (funExt (λ {(dir , pr) →  toProve dir pr  })))) 
            where
                theRightB : ∀ {dir : direction r posR} → forgetLeft (recoverLeft (f dir) (λ pr₁ → g (dir , toImpossibleRight pr₁))) ≡ inj₁ tt
                theRightB {dir} = {! !}
                lemma : ∀{a} → transp (λ i → direction p posP) i0 a ≡ a
                lemma {a} = transportRefl a
                lemma4 : ∀{dir : direction r posR} {a} {b} →
                    keepLeft (recoverLeft (f (transp (λ i → direction r posR) i0 dir))
                        (λ pr₁ →
                           g
                           ((transp (λ i → direction r posR) i0 dir) , toImpossibleRight pr₁)))
                    a
                    ≡
                    keepLeft (recoverLeft (f dir)
                        (λ pr₁ →
                           g
                           (dir , toImpossibleRight pr₁)))
                    b
                lemma4 = {!   !}

                -- With all constant transp removed
                toProve2 : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) → 
                    (keepLeft (recoverLeft (f dir) (λ pr₁ → g (dir , toImpossibleRight pr₁)))
                    (fromImpossibleRight
                        (subst [ (λ _ → ⊤) , (λ _ → ⊥) ] (sym $ forgetRecoverLeft2 (f dir) (λ y → g (dir , toImpossibleRight y))) pr)
                    ))
                    ≡ g (dir , pr)
                toProve2 dir pr = {!   !}

                toProve3 : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) →
                    keepLeft (recoverLeft (f (transport (λ i → direction r posR) dir))
                        (λ pr₁ →
                            g
                            (transport (λ i → direction r posR) dir , toImpossibleRight pr₁)))
                        (fromImpossibleRight
                        (transport
                            (λ i →
                            [ (λ _ → ⊤) , (λ _ → ⊥) ]
                            (forgetRecoverLeft2
                                (f (transp (λ i₃ → direction r posR) (~ i) dir))
                                (λ y →
                                g
                                (transp (λ i₃ → direction r posR) (~ i) dir , toImpossibleRight y))
                                (~ i)))  pr))
                        ≡
                    keepLeft (recoverLeft (f dir) (λ pr₁ → g (dir , toImpossibleRight pr₁)))
                        (fromImpossibleRight
                        (transport
                            (λ i →
                            [ (λ _ → ⊤) , (λ _ → ⊥) ]
                            (forgetRecoverLeft2 (f dir) (λ y → g (dir , toImpossibleRight y))
                                (~ i)))
                            pr))
                toProve3 dir pr = {! refl  !}
                toProve : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) → transp (λ i → direction p posP) i0
                    (keepLeft
                    (recoverLeft (f (transp (λ i → direction r posR) i0 dir))
                        (λ pr₁ →
                        g
                        (transp (λ i → direction r posR) i0 dir , toImpossibleRight pr₁)))
                    (fromImpossibleRight
                        (transp
                        (λ i →
                            [ (λ _ → ⊤) , (λ _ → ⊥) ]
                            (forgetRecoverLeft2
                            (f (transp (λ i₃ → direction r posR) (~ i) dir))
                            (λ y →
                                g
                                (transp (λ i₃ → direction r posR) (~ i) dir , toImpossibleRight y))
                            (~ i)))
                        i0 pr)))
                    ≡ g (dir , pr)
                toProve dir pr = lemma ∙ toProve3 dir pr ∙ toProve2 dir pr

                

                -- toProve3 : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) → 

                --     (λ pr₁ → g (dir , toImpossibleRight pr₁))
                --     (subst (λ x₂ → x₂ ≡ inj₁ tt) forgetRecoverLeft a)
                --     (fromImpossibleRight
                --         (transp (λ i → [ (λ _ → ⊤) , (λ _ → ⊥) ] (forgetRecoverLeft2 (f dir) (λ y → g (dir , toImpossibleRight y)) (~ i))) i0 pr)
                --     )
                --     ≡ g (dir , pr)
                -- toProve3 dir pr = {!   !} ∙ {!   !}

                -- toProve : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) → transp (λ i → direction p posP) i0
                --     (keepLeft
                --     (recoverLeft (f (transp (λ i → direction r posR) i0 dir))
                --         (λ pr₁ →
                --         g
                --         (transp (λ i → direction r posR) i0 dir , toImpossibleRight pr₁)))
                --     (fromImpossibleRight
                --         (transp (λ i → [ (λ _ → ⊤) , (λ _ → ⊥) ] (forgetRecoverLeft {x = {!   !}} (~ i)))
                --         i0 pr)))
                --     ≡ g (dir , pr)
                -- toProve = {!   !}
                




                -- hej : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) → (transp (λ i → [ (λ _ → ⊤) , (λ _ → ⊥) ] (forgetRecoverLeft (~ i))) i0 pr) ≡ {!   !}
                -- hej = {!   !}

                -- yo : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) → (λ { (dir , snd₁)
                --             → keepLeft (snd (go posP posQ ((posR , f) , g)) dir)
                --             (fromImpossibleRight snd₁)
                --         })
                --     (transp
                --     (λ j →
                --         direction (r ◂ Y + Constant (direction q posQ))
                --         (ΣPathP
                --         ((λ _ → proj₁ (go posP posQ ((posR , f) , g))) ,
                --             funExt (λ x → forgetRecoverLeft))
                --         (~ j)))
                --     i0 (dir , pr))
                --     ≡ g (dir , pr)
                -- yo = {!   !}

                -- lemma2 : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) → 
                --     keepLeft
                --         (recoverLeft (f (transp (λ i → direction r posR) i0 dir)) (λ pr₁ → g (transp (λ i → direction r posR) i0 dir , toImpossibleRight pr₁)))
                --         (fromImpossibleRight (transp (λ i → [ (λ _ → ⊤) , (λ _ → ⊥) ] (forgetRecoverLeft {x = f dir } {f = {!   !}} (~ i))) i0 pr)
                --         )
                --         ≡ g (dir , pr)
                -- lemma2 = {!   !}



                -- lemma2 : (dir : direction r posR) → ∀{a} → keepLeft (recoverLeft (f {! transp (λ i → direction r posR) i0 dir  !}) a) ≡ keepLeft (recoverLeft (f dir) a) -- ? ≡ ̄?   -- keepLeft (recoverLeft (f (transp (λ i → direction r posR) i0 dir))) ? ≡ keepLeft (recoverLeft (f dir)) a
                -- lemma2 = {!   !}

                -- lemma3 : (dir : direction r posR) (pr : [ (λ _ → ⊤) , (λ _ → ⊥) ] (f dir)) → 
                --     keepLeft (recoverLeft (f (transp (λ i → direction r posR) i0 dir))
                --         (λ (pr₁ : f (transp (λ i → direction r posR) i0 dir) ≡ inj₁ tt) →
                --             g
                --             (transp (λ i → direction r posR) i0 dir , toImpossibleRight pr₁)))
                --     (fromImpossibleRight
                --     (transp (λ i → [ (λ _ → ⊤) , (λ _ → ⊥) ] (forgetRecoverLeft (~ i)))
                --         i0 pr))
                --     ≡ g (dir , pr)
                -- lemma3 = {!   !}
                    -- where
                    --     open import Level
                    --     lemma4 : (transp (λ i → [_,_] {zero} {{! ⊤  !}} (λ _ → ⊤) (λ _ → ⊥) (forgetRecoverLeft (~ i))) i0 pr) ≡ pr
                    --     lemma4 = transportRefl (sym pr)
                -- lemma4 : ∀{a dir} →
                --     keepLeft (recoverLeft (f (transp (λ i → direction r posR) i0 dir))
                --         (λ (pr₁ : f (transp (λ i → direction r posR) i0 dir) ≡ inj₁ tt) →
                --             g
                --             ((transp (λ i → direction r posR) i0 dir) , toImpossibleRight pr₁)))
                --     a
                --     -- (transp (λ i → [ (λ _ → ⊤) , (λ _ → ⊥) ] (forgetRecoverLeft (~ i)))
                --     --     i0 pr))
                --     ≡
                --     keepLeft (recoverLeft (f dir)
                --         (λ (pr₁ : f dir ≡ inj₁ tt) →
                --             g
                --             (dir , toImpossibleRight pr₁)))
                --     a
                --     --  g (dir , pr)
                -- lemma4 = {!   !}

       

-- By 2.84
four' : ((i : position p) (j : position q) → Σ[ k ∈ position r ] ((direction r k) → (direction p i) ⊎ (direction q j)))
      ≡ ((i×j : position (p * q)) → Σ[ k ∈ position r ] (direction r k → direction (p * q) i×j))
four' {p} {q} = π≡ (funExt (λ posP → π≡ (funExt λ posQ → refl))) ∙ groupPi

-- By 2.54
five' : (((i , j) : position (p * q)) → Σ[ k ∈ position r ] (direction r k → direction (p * q) ((i , j))))
      ≡ Lens (p * q) r
five' = sym prop254

-- Page 131
chain' : {p q r : Polynomial} → Lens p (r ^ q) ≡ Lens (p * q) r
chain' = zero' ∙ one' ∙ two' ∙ three' ∙ four' ∙ five'


---------------- End clean attempt



-- -- two' : {p q r : Polynomial} → ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ◂ Y + Constant (direction q j))) ≡ (((i : position p) → (j : position q) →  {!   !} ))
-- -- two' = {!   !}


-- one : {p q r : Polynomial} → Lens p (r ^ q) ≡ ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ^ q))
-- one {p} {q} {r} = isoToPath (iso go
--                                  back
--                                  pgoback
--                                  λ a → refl)
--     where go : (x : Lens p (r ^ q)) (x₁ : position p) (x₂ : position q) → Lens (purePower (direction p x₁)) (r ^ q)
--           go (f ⇆ f♯) i j = (λ _ → f i) ⇆ (λ _ x → f♯ i x)
--           back : ((x₁ : position p) → position q → Lens (purePower (direction p x₁)) (r ^ q)) → Lens p (r ^ q)
--           back f = mp ⇆ md
--                 where mp : (x : position p) → position (r ^ q)
--                       mp x index = mapPosition (f x index) tt index
--                       md : (fromPos : position p) → direction (r ^ q) (mp fromPos) → direction p fromPos
--                       md fromPos (posQ , dirR , x) = mapDirection (f fromPos posQ) tt (posQ , dirR , x)
--           pgoback : (b : (x₁ : position p) → position q → Lens (purePower (direction p x₁)) (r ^ q)) → go (back b) ≡ b
--           pgoback b = {!   !}

-- -- two' : {p q r : Polynomial} → ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ^ q)) ≡ ((i : position p) → (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆)
-- -- two' = ?

-- two : {p q r : Polynomial} → ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ^ q)) ≡ ((i : position p) → (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆)
-- two {p} {q} {r} = isoToPath (iso go
--                                  back
--                                  {!   !}
--                                  {!   !})
--     where go : ((i : position p) → position q → Lens (purePower (direction p i)) (r ^ q)) → (i : position p) (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆
--           go f posP posQ = fst (mapPosition (f posP posQ) tt posQ) , λ x → sol x
--              where smth : direction (r ^ q) (mapPosition (f posP posQ) tt) → direction p posP
--                    smth = mapDirection (f posP posQ) tt
--                    sol : (x : direction r (fst (mapPosition (f posP posQ) tt posQ))) → direction p posP ⊎ direction q posQ
--                    sol x with (snd (mapPosition (f posP posQ) tt posQ) x) in eq
--                    ... | inj₁ x₁ = inj₁ $ (mapDirection (f posP posQ) tt) (posQ , x , help)
--                        where help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (mapPosition (f posP posQ) tt posQ) x)
--                              help rewrite eq = tt
--                    ... | inj₂ y = inj₂ y
--           back : ((i : position p) (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆) → (i : position p) → position q → Lens (purePower (direction p i)) (r ^ q)
--           back f posP posQ = (λ x index → (fst (f posP index)) , (λ x₁ → inj₁ tt)) ⇆ λ fromPos x → {!   !}




-- helpgo : {p q r : Polynomial} (f : position p → position (r ^ q)) (i : position p) (j : position q) →  (x : direction r (fst (f i j))) → ⊤ ⊎ direction q j
-- helpgo {p} {q} {r} f i j = {!   !}

-- anything : {A : Set} (ta : ⊤ ⊎ A) → [ (λ _ → ⊤) , (λ _ → ⊥) ] ta → ⊤
-- anything (inj₁ x) pr = x

-- anything2 : {A : Set} (ta : ⊤ ⊎ A) → [ (λ _ → ⊤) , (λ _ → ⊥) ] ta → ta ≡ inj₁ tt
-- anything2 (inj₁ x) pr = refl

-- letsgo : {p q r : Polynomial} → Lens p (r ^ q) → ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j)))
-- letsgo {p} {q} {r} (f ⇆ f♯) i j = (fst (f i j)) , find
--     where find : (x : direction r (fst (f i j))) → direction p i ⊎ direction q j
--           find x with snd (f i j) x in eq
--           ... | inj₁ x₁ = inj₁ (f♯ i (j , x , transport {!  anything2 (snd (f i j) x)  !} ((snd (f i j) x))))
--               where help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (f i j) x)
--                     help rewrite eq = tt
--           ... | inj₂ y = inj₂ y

-- import Relation.Binary.PropositionalEquality as Eq

-- onethree : {p q r : Polynomial} → Lens p (r ^ q) ≡ ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j)))
-- onethree {p} {q} {r} = isoToPath (iso letsgo
--                                       back 
--                                       pr
--                                       (λ { (f ⇆ f♯) → lensesEqual3 (funExt λ x → {!  !}) {!   !} }))
--     where back : ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j))) → Lens p (r ^ q)
--           back f = mp ⇆ md
--                where mp : position p → position (r ^ q)
--                      mp posP index = fst (f posP index) , dirb
--                         where dirb : direction r (fst (f posP index)) → ⊤ ⊎ direction q index
--                               dirb dir = eraseLeft $ snd (f posP index) dir
--                      md : (fromPos : position p) → direction (r ^ q) (mp fromPos) → direction p fromPos
--                      md fp (posQ , dirExp) = convGeneral (snd (f fp posQ) (fst dirExp)) (snd dirExp)
--           pr : section letsgo back
--           pr b = funExt help
--              where help : (x : position p) → letsgo (back b) x ≡ b x
--                    help posP = funExt help2
--                         where help2 : (x : position q) → letsgo (back b) posP x ≡ b posP x
--                               help2 posQ =  ΣPathP (refl , funExt help3 )
--                                 where help3 : (x : direction r (fst (letsgo (back b) posP posQ))) → snd (letsgo (back b) posP posQ) x ≡ snd (b posP posQ) x
--                                       help3 k with snd (letsgo (back b) posP posQ) k
--                                       ... | inj₁ x3  = {!   !}
--                                           where help4 : inj₁ x3 ≡ snd (b posP posQ) k 
--                                                 help4 with snd (b posP posQ) k
--                                                 ... | sm = {!   !}
--                                       ... | inj₂ y  = {!   !}
                                      

-- four : {p q r : Polynomial} → ((i : position p) → (j : position q) → Σ[ k ∈ position r ] ( direction r k → (direction p i ⊎ direction q j))) ≡ ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) )
-- four {p} {q} {r} = isoToPath (iso go
--                                  back
--                                  (λ b → refl)
--                                  λ a → refl)
--     where go : ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j))) → ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) )
--           go x (fst₁ , snd₁) = (fst (x fst₁ snd₁)) , snd (x fst₁ snd₁)
--           back : ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) ) → ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j)))
--           back x i j = x ( i , j )

-- five : {p q r : Polynomial} → ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ] ( direction r k → direction (p * q) ( i , j ) ) ) ≡ Lens (p * q) r
-- five {p} {q} {r} = isoToPath (iso go
--                                  back
--                                  (λ b → refl)
--                                  λ a → refl)
--     where go :  ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) ) → Lens (p * q) r
--           go f = mp ⇆ md
--             where mp : position (p * q) → position r
--                   mp (i , j) = fst $ f ( i , j )
--                   md : (fromPos : position (p * q)) → direction r (mp fromPos) → direction (p * q) fromPos
--                   md fp d = snd (f fp) d
--           back : Lens (p * q) r → ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) )
--           back (f ⇆ f♯) (i , j) = (f (i , j)) , (f♯ (i , j))
                                
-- chain2 : {p q r : Polynomial} → Lens p (r ^ q) ≡ Lens (p * q) r
-- chain2 {p} {q} {r} = isoToPath (iso go 
--                                     back
--                                     (λ b → lensesEqual3 refl {!   !})
--                                     λ a → lensesEqual3 {!   !} {!   !})
--     where go : Lens p (r ^ q) → Lens (p * q) r
--           go (f ⇆ f♯) = mp ⇆ md
--              where mp : position (p * q) → position r
--                    mp (posp , posq) = fst $ f posp posq
--                    md : (fromPos : position (p * q)) → direction r (mp fromPos) → direction (p * q) fromPos
--                    md (posp , posq) dir with snd (f posp posq) dir in eq
--                    ... | inj₁ tt = inj₁ (f♯ posp (posq , (dir , help)))
--                       where help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (f posp posq) dir)
--                             help rewrite eq = tt
--                    ... | inj₂ y = inj₂ y
--           back : Lens (p * q) r → Lens p (r ^ q)
--           back (f ⇆ f♯) = mp ⇆ md
--               where mp : position p → position (r ^ q)
--                     mp posp index = (f (posp , index)) , (λ x → eraseLeft $ f♯ (posp , index) x)
--                     md : (fromPos : position p) → direction (r ^ q) (mp fromPos) → direction p fromPos
--                     md fp (posq , dirR , pr) = convGeneral (f♯ (fp , posq) dirR) pr

-- -- Page 131
-- chain : {p q r : Polynomial} → Lens p (r ^ q) ≡ Lens (p * q) r
-- chain = one ∙ two ∙ three ∙ four ∙ five
   