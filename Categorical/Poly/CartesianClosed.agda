{-# OPTIONS --cubical #-}

module Categorical.Poly.CartesianClosed where

open import CategoryData.Everything
open import Categorical.Poly.Instance

import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Cubical.Data.Sigma hiding (_×_)
open import Cubical.Data.Sigma.Properties
open import Cubical.Foundations.Isomorphism
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Product hiding (Σ-syntax ; curry ; uncurry)
open import Categorical.Poly.Product
open import Categories.Object.Product Poly
open import Categorical.Poly.Terminal
open import Cubical.Proofs
open import Cubical.LensEquality
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
import Categories.Category.CartesianClosed.Canonical Poly as Canonical
open import Function
open import Cubical.Functions.FunExtEquiv
open import Cubical.Utils.CoproductUtils

open Polynomial

univPropCoproduct : {p q : Polynomial} → Lens p q ≡ ((i : position p) → Lens (purePower (direction p i)) q)
univPropCoproduct {p} {q} = isoToPath (iso go back (λ b → refl) λ a → refl)
      where 
        go : Lens p q → (i : position p) → Lens (purePower (direction p i)) q
        go (f ⇆ f♯) = λ i → (const (f i)) ⇆ const (f♯ i)

        back : ((i : position p) → Lens (purePower (direction p i)) q) → Lens p q
        back pit = ( (λ y → mapPosition y tt) ∘  pit) ⇆ ((λ y → mapDirection y tt) ∘ pit)

yoneda : {q : Polynomial} {i : Set} → Lens (purePower i) q ≡ q ⦅ i ⦆
yoneda {q} {i} = isoToPath (iso go back (λ _ → refl) (λ _ → refl))
      where 
        go : Lens (purePower (i)) q → q ⦅ i ⦆
        go (f ⇆ f♯) = (f tt) , (f♯ tt)

        back : q ⦅ i ⦆ → Lens (purePower (i)) q
        back (posq , mapdir) = const posq ⇆ λ fromPos x → mapdir x

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
zero : Lens p (r ^ q)
     ≡ Lens p (ΠPoly (position q , λ j → r ◂ Y + Constant (direction q j)))
zero = refl

-- By universal property of products and coproducts.  
one : Lens p (ΠPoly (position q , λ j → r ◂ Y + Constant (direction q j)))
     ≡ ((i : position p) (j : position q) → Lens (purePower (direction p i)) (r ◂ Y + Constant (direction q j)))
one = univPropCoproduct ∙ π≡ (funExt (λ x → universalPropertyProduct))

-- By yoneda lemma.
two : ((i : position p) (j : position q) → Lens (purePower (direction p i)) (r ◂ Y + Constant (direction q j)))
     ≡ ((i : position p) (j : position q) → (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆)
two = π≡ (funExt (λ posP → π≡ (funExt (λ posQ → yoneda))))

three : ((i : position p) (j : position q) → (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆)
       ≡ ((i : position p) (j : position q) → Σ[ k ∈ position r ] ((direction r k) → (direction p i) ⊎ (direction q j)))
three {p} {q} {r} = π≡ (funExt (λ x → π≡ (funExt (λ y → lemma x y)))) 
    where

        lemma : (x : position p) (y : position q)
            → (r ◂ Y + Constant (direction q y)) ⦅ direction p x ⦆
            ≡ (Σ[ k ∈ position r ]  (direction r k → direction p x ⊎ direction q y))
        lemma x y = ΣAssoc ∙ cong (Σ (position r)) (funExt (λ z → withΣOfFunction ))
            where
                extractFunction : {A B X : Set}
                    → (Σ[ b ∈ (X → ⊤ ⊎ B) ]
                         (Σ[ a ∈ X ]
                            ([ (λ _ → ⊤) , (λ _ → ⊥) ] (b a)) → A))
                       ≡ (X → Σ[ b ∈ (⊤ ⊎ B) ] (([ (λ _ → ⊤) , (λ _ → ⊥) ] b) → A))
                extractFunction = isoToPath (iso (λ (x , y) z → x z , λ c → y (z , c)) (λ d → (λ e → fst (d e)) , λ (f , g) → snd (d f) g) (λ b  → refl) λ a → refl)

                withΣOfFunction : {A B X : Set}
                    → (Σ[ b ∈ (X → ⊤ ⊎ B) ] (Σ[ a ∈ X ] ([ (λ _ → ⊤) , (λ _ → ⊥) ] (b a)) → A))
                        ≡ (X → A ⊎ B)
                withΣOfFunction = extractFunction ∙ π≡ (funExt (λ x → ΣforgetAndRememberSame))

-- By 2.84
four : ((i : position p) (j : position q) → Σ[ k ∈ position r ] ((direction r k) → (direction p i) ⊎ (direction q j)))
      ≡ ((i×j : position (p * q)) → Σ[ k ∈ position r ] (direction r k → direction (p * q) i×j))
four {p} {q} = π≡ (funExt (λ posP → π≡ (funExt λ posQ → refl))) ∙ groupPi

-- By 2.54
five : (((i , j) : position (p * q)) → Σ[ k ∈ position r ] (direction r k → direction (p * q) ((i , j))))
      ≡ Lens (p * q) r
five = sym prop254

-- Page 131
cartesianClosed : {p q r : Polynomial} → Lens p (r ^ q) ≡ Lens (p * q) r
cartesianClosed = zero ∙ one ∙ two ∙ three ∙ four ∙ five

-- Exercise 4.31, page 131.
-- The canonical evaluation map is the identity lens transported through the cartesian closure.
eval' : {p q : Polynomial} → Lens ((q ^ p) * p) q
eval' {p} {q} = subst (λ x → x) path idLens'
    where
        path : Lens (q ^ p) (q ^ p) ≡ Lens (q ^ p * p) q
        path = (cartesianClosed {q ^ p} {p} {q})

        idLens' : Lens (q ^ p) (q ^ p)
        idLens' = idLens {q ^ p}

-- Some direct definitions of eval, curry & uncurry
eval : {p q : Polynomial} → Lens ((q ^ p) * p) q
eval {p} {q} = mapPos ⇆ mapDir
    where
        mapPos : position ((q ^ p) * p) → position q
        mapPos (posQ^P , posP) = fst (posQ^P posP)

        mapDir : (pos : position ((q ^ p) * p))
            → direction q (mapPos pos) 
            → direction ((q ^ p) * p) pos
        mapDir (posQ^P , posP) dir = recoverLeft (snd (posQ^P posP) dir) λ x → posP , dir , x

curry : {p q r : Polynomial} → Lens (p * q) r → Lens p (r ^ q)
curry {p} {q} {r} (f ⇆ f♯) = mapPos ⇆ mapDir
    where
        mapPos : position p → position (r ^ q)
        mapPos posP posQ = f (posP , posQ) , λ {dirR → forgetLeft  (f♯ (posP , posQ) dirR)}

        mapDir : (pos : position p) → direction (r ^ q) (mapPos pos) → direction p pos
        mapDir posP (posQ , dirR , g) = keepLeft (f♯ (posP , posQ) dirR) g

uncurry : {p q r : Polynomial} → Lens p (q ^ r) → Lens (p * r) q
uncurry {p} {q} {r} (f ⇆ f♯) = mapPos ⇆ mapDir
    where
        mapPos : position (p * r) → position q
        mapPos (posP , posR) = fst (f posP posR)

        mapDir : (pos : position (p * r)) → direction q (mapPos pos) → direction (p * r) pos
        mapDir (posP , posR) dirQ = recoverLeft (snd (f posP posR) dirQ) λ x → f♯ posP (posR , dirQ , x)

uncurry₂ : {p q r : Polynomial} → Lens r (q ^ p) → Lens (r * p) q
uncurry₂ h = eval ∘ₚ ⟨ h × idLens ⟩