{-# OPTIONS --cubical #-}

module Categorical.CartesianClosed where

open import CategoryData.Everything
open import Categorical.Instance.Poly

import Relation.Binary.PropositionalEquality as Eq
open import Categories.Object.Exponential Poly
open import Cubical.Data.Sigma
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

open Polynomial
depProd : Σ[ ind ∈ Set ](ind → Polynomial) → Polynomial
depProd (ind , polyAt) = mkpoly ((i : ind) → position (polyAt i))
                                      (λ a⁺ → Σ[ i ∈ ind ](direction (polyAt i) (a⁺ i)))
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
univPropProduct {p} {q} {qi} = isoToPath (iso go
                                              back
                                              (λ b → refl) 
                                              λ a → refl)
      where go : Lens p (ΠPoly (position q , qi)) → (i : position q) → Lens p (qi i)
            go (f ⇆ f♯) = λ i → (λ x → f x i) ⇆ λ fromPos x → f♯ fromPos (i , x)
            back : ((i : position q) → Lens p (qi i)) → Lens p (ΠPoly (position q , qi))
            back f = (λ z index → mapPosition (f index) z) ⇆ λ { fromPos (fst₁ , snd₁) → mapDirection (f fst₁) fromPos snd₁ }
-- ΠPoly (posQ , λ j → r ◂ (Y + Constant (dirQ j)))
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

wrong : {p q r : Polynomial} → ((i : position p) → (j : position q) → (r ◂ (Y + Constant (direction q j))) ⦅ direction p i ⦆ ) ≡ ((i : position p) → (j : position q) → (r ⦅ direction q j  ⊎ direction p i ⦆ ))
wrong {p} {q} {r} = isoToPath (iso go 
                                   {!   !}
                                   {!   !}
                                   {!   !})
  where go : ((i : position p) (j : position q) → (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆) → (i : position p) (j : position q) → r ⦅ direction q j ⊎ direction p i ⦆
        go exx = λ i j → (fst $ fst (exx i j)) , λ { x → (λ { y → {! y  !} }) ∘ snd $ exx i j }
        back : ((i : position p) (j : position q) → r ⦅ direction q j ⊎ direction p i ⦆) → (i : position p) (j : position q) → (r ◂ Y + Constant (direction q j)) ⦅ direction p i ⦆
        back exxx = {!   !}

thr : {p q r : Polynomial} → ((i : position p) → (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆) ≡ ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j)))
thr {p} {q} {r} = isoToPath (iso (λ x i j → (fst $ x i j) , (λ x₁ → snd (x i j) x₁)) 
                                 (λ x i j → x i j) 
                                 {!   !} 
                                 λ a → refl)

one : {p q r : Polynomial} → Lens p (r ^ q) ≡ ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ^ q))
one {p} {q} {r} = isoToPath (iso go
                                 back
                                 pgoback
                                 λ a → refl)
    where go : (x : Lens p (r ^ q)) (x₁ : position p) (x₂ : position q) → Lens (purePower (direction p x₁)) (r ^ q)
          go (f ⇆ f♯) i j = (λ _ → f i) ⇆ (λ _ x → f♯ i x)
          back : ((x₁ : position p) → position q → Lens (purePower (direction p x₁)) (r ^ q)) → Lens p (r ^ q)
          back f = mp ⇆ md
                where mp : (x : position p) → position (r ^ q)
                      mp x index = mapPosition (f x index) tt index
                      md : (fromPos : position p) → direction (r ^ q) (mp fromPos) → direction p fromPos
                      md fromPos (posQ , dirR , x) = mapDirection (f fromPos posQ) tt (posQ , dirR , x)
          pgoback : (b : (x₁ : position p) → position q → Lens (purePower (direction p x₁)) (r ^ q)) → go (back b) ≡ b
          pgoback b = {!   !}

two : {p q r : Polynomial} → ((i : position p) → (j : position q) → Lens (purePower (direction p i)) (r ^ q)) ≡ ((i : position p) → (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆)
two {p} {q} {r} = isoToPath (iso go
                                 back
                                 {!   !}
                                 {!   !})
    where go : ((i : position p) → position q → Lens (purePower (direction p i)) (r ^ q)) → (i : position p) (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆
          go f posP posQ = fst (mapPosition (f posP posQ) tt posQ) , λ x → sol x
             where smth : direction (r ^ q) (mapPosition (f posP posQ) tt) → direction p posP
                   smth = mapDirection (f posP posQ) tt
                   sol : (x : direction r (fst (mapPosition (f posP posQ) tt posQ))) → direction p posP ⊎ direction q posQ
                   sol x with (snd (mapPosition (f posP posQ) tt posQ) x) in eq
                   ... | inj₁ x₁ = inj₁ $ (mapDirection (f posP posQ) tt) (posQ , x , help)
                       where help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (mapPosition (f posP posQ) tt posQ) x)
                             help rewrite eq = tt
                   ... | inj₂ y = inj₂ y
          back : ((i : position p) (j : position q) → r ⦅ direction p i ⊎ direction q j ⦆) → (i : position p) → position q → Lens (purePower (direction p i)) (r ^ q)
          back f posP posQ = (λ x index → (fst (f posP index)) , (λ x₁ → inj₁ tt)) ⇆ λ fromPos x → {!   !}

helpgo : {p q r : Polynomial} (f : position p → position (r ^ q)) (i : position p) (j : position q) →  (x : direction r (fst (f i j))) → ⊤ ⊎ direction q j
helpgo {p} {q} {r} f i j = {!   !}

anything : {A : Set} (ta : ⊤ ⊎ A) → [ (λ _ → ⊤) , (λ _ → ⊥) ] ta → ⊤
anything (inj₁ x) pr = x

anything2 : {A : Set} (ta : ⊤ ⊎ A) → [ (λ _ → ⊤) , (λ _ → ⊥) ] ta → ta ≡ inj₁ tt
anything2 (inj₁ x) pr = refl

letsgo : {p q r : Polynomial} → Lens p (r ^ q) → ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j)))
letsgo {p} {q} {r} (f ⇆ f♯) i j = (fst (f i j)) , find
    where find : (x : direction r (fst (f i j))) → direction p i ⊎ direction q j
          find x with snd (f i j) x in eq
          ... | inj₁ x₁ = inj₁ (f♯ i (j , x , transport {!  anything2 (snd (f i j) x)  !} ((snd (f i j) x))))
              where help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (f i j) x)
                    help rewrite eq = tt
          ... | inj₂ y = inj₂ y

import Relation.Binary.PropositionalEquality as Eq

onethree : {p q r : Polynomial} → Lens p (r ^ q) ≡ ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j)))
onethree {p} {q} {r} = isoToPath (iso letsgo
                                      back 
                                      pr
                                      (λ { (f ⇆ f♯) → lensesEqual3 (funExt λ x → {!  !}) {!   !} }))
    where back : ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j))) → Lens p (r ^ q)
          back f = mp ⇆ md
               where mp : position p → position (r ^ q)
                     mp posP index = fst (f posP index) , dirb
                        where dirb : direction r (fst (f posP index)) → ⊤ ⊎ direction q index
                              dirb dir = eraseLeft $ snd (f posP index) dir
                     md : (fromPos : position p) → direction (r ^ q) (mp fromPos) → direction p fromPos
                     md fp (posQ , dirExp) = convGeneral (snd (f fp posQ) (fst dirExp)) (snd dirExp)
          pr : section letsgo back
          pr b = funExt help
             where help : (x : position p) → letsgo (back b) x ≡ b x
                   help posP = funExt help2
                        where help2 : (x : position q) → letsgo (back b) posP x ≡ b posP x
                              help2 posQ =  ΣPathP (refl , funExt help3 )
                                where help3 : (x : direction r (fst (letsgo (back b) posP posQ))) → snd (letsgo (back b) posP posQ) x ≡ snd (b posP posQ) x
                                      help3 k with snd (letsgo (back b) posP posQ) k
                                      ... | inj₁ x3  = {!   !}
                                          where help4 : inj₁ x3 ≡ snd (b posP posQ) k 
                                                help4 with snd (b posP posQ) k
                                                ... | sm = {!   !}
                                      ... | inj₂ y  = {!   !}
                                      

for : {p q r : Polynomial} → ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j))) ≡ ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) )
for {p} {q} {r} = isoToPath (iso go
                                 back
                                 (λ b → refl)
                                 λ a → refl)
    where go : ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j))) → ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) )
          go x (fst₁ , snd₁) = (fst (x fst₁ snd₁)) , snd (x fst₁ snd₁)
          back : ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) ) → ((i : position p) → (j : position q) → Σ[ k ∈ position r ]( direction r k → (direction p i ⊎ direction q j)))
          back x i j = x ( i , j )

fiv : {p q r : Polynomial} → ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) ) ≡ Lens (p * q) r
fiv {p} {q} {r} = isoToPath (iso go
                                 back
                                 (λ b → refl)
                                 λ a → refl)
    where go :  ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) ) → Lens (p * q) r
          go f = mp ⇆ md
            where mp : position (p * q) → position r
                  mp (i , j) = fst $ f ( i , j )
                  md : (fromPos : position (p * q)) → direction r (mp fromPos) → direction (p * q) fromPos
                  md fp d = snd (f fp) d
          back : Lens (p * q) r → ((( i , j ) : position (p * q)) → Σ[ k ∈ position r ]( direction r k → direction (p * q) ( i , j ) ) )
          back (f ⇆ f♯) (i , j) = (f (i , j)) , (f♯ (i , j))
                                
chain2 : {p q r : Polynomial} → Lens p (r ^ q) ≡ Lens (p * q) r
chain2 {p} {q} {r} = isoToPath (iso go 
                                    back
                                    (λ b → lensesEqual3 refl {!   !})
                                    λ a → lensesEqual3 {!   !} {!   !})
    where go : Lens p (r ^ q) → Lens (p * q) r
          go (f ⇆ f♯) = mp ⇆ md
             where mp : position (p * q) → position r
                   mp (posp , posq) = fst $ f posp posq
                   md : (fromPos : position (p * q)) → direction r (mp fromPos) → direction (p * q) fromPos
                   md (posp , posq) dir with snd (f posp posq) dir in eq
                   ... | inj₁ tt = inj₁ (f♯ posp (posq , (dir , help)))
                      where help : [ (λ _ → ⊤) , (λ _ → ⊥) ] (snd (f posp posq) dir)
                            help rewrite eq = tt
                   ... | inj₂ y = inj₂ y
          back : Lens (p * q) r → Lens p (r ^ q)
          back (f ⇆ f♯) = mp ⇆ md
              where mp : position p → position (r ^ q)
                    mp posp index = (f (posp , index)) , (λ x → eraseLeft $ f♯ (posp , index) x)
                    md : (fromPos : position p) → direction (r ^ q) (mp fromPos) → direction p fromPos
                    md fp (posq , dirR , pr) = convGeneral (f♯ (fp , posq) dirR) pr

chain : {p q r : Polynomial} → Lens p (r ^ q) ≡ Lens (p * q) r
chain {p} {q} {r} = isoToPath (compIso (pathToIso one)
                                       (compIso (pathToIso two) 
                                                (compIso (pathToIso thr) 
                                                         (compIso (pathToIso for)  (pathToIso fiv)))))

canonical : {A B : Polynomial} → Canonical.CartesianClosed
canonical {A} {B} = record
    { ⊤ = 𝟙
    ; _×_ = _*_
    ; ! = lensToOne
    ; π₁ = π₁
    ; π₂ = π₂
    ; ⟨_,_⟩ = ⟨_,_⟩
    ; !-unique = lensToOneUnique
    ; π₁-comp = refl
    ; π₂-comp = refl
    ; ⟨,⟩-unique = unique
    ; _^_ = _^_
    ; eval = eval
    ; curry = curry
    ; eval-comp =  {!   !}
    ; curry-resp-≈ = cong curry
    ; curry-unique = {!   !}
    }
       where
        curry-unique-simple : {p q r : Polynomial} → {f : Lens p (q ^ r)} → {g : Lens (p * r) q} → eval ∘ₚ (⟨ f × idLens ⟩) ≡ g → f ≡ curry g
        curry-unique-simple {p} {q} {r} {f = f ⇆ f♯} {g = g ⇆ g♯} proof = lensesEqual3 mapPos≡ {!   !}
           where mapPos≡ : f ≡ mapPosition (curry (g ⇆ g♯))
                 mapPos≡ = pr 
                   where pr = funExt xtopr
                            where xtopr : (x : position p) → f x ≡ mapPosition (curry (g ⇆ g♯)) x
                                  xtopr x = funExt rtoprr
                                     where rtoprr : (posr : position r) → f x posr ≡ mapPosition (curry (g ⇆ g♯)) x posr
                                           rtoprr rr = {!   !}
                                                    where mpcurr : position p → (index : position r) → Σ (position q) (λ i → direction q i → ⊤ ⊎ direction r index)
                                                          mpcurr = mapPosition (curry (g ⇆ g♯))
                                                          posq : position q
                                                          posq = fst $ mpcurr x rr
                                                          lem : posq ≡ (fst $ f x rr)
                                                          lem = {!   !}
                    --  where xtopr : (x : position p) → 
                    --             where mpcurr : position p → (index : position r) → Σ (position q) (λ i → direction q i → ⊤ ⊎ direction r index)
                    --                   mpcurr = mapPosition (curry (g ⇆ g♯))
                    --                   posq : position q
                    --                   posq = mpcurr x y
                         
                 
        -- ... | (s ⇆ s♯) = ? ⇆ {!   !}
            -- where mp : position p → (index : position r) → Σ (position q) (λ i₃ → direction q i₃ → ⊤ ⊎ direction r index)
            --       mp p ind with s ( p , ind )
            --       ... | a = a , {!   !}
            --       md = {!   !}
        -- eval-comp-simple : {C D E : Polynomial} → 
        --             (f : Lens (E * D) C) → 
        --             (ev ∘ₚ ⟨ curry f × idLens ⟩)
        --             ≡ f
        -- eval-comp-simple {C} {D} {E} f = lensesEqual3 refl mapDir≡
        --     where
        --         mapDir≡ : (x : position (E * D))
        --                 → (y : direction C (mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩) x))
        --                 → mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩)
        --                                x 
        --                                (subst (λ mapPos → direction C (mapPos x)) (sym (λ _ → mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩))) y)
        --                     ≡ 
        --                   mapDirection f x y
        --         mapDir≡ x@(posE , posD) y = {!   !}
        --         mapDir≡' : (x : position (E * D))
        --                 → (y : direction C (mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩) x))
        --                 → mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩)
        --                                x 
        --                                y
        --                     ≡ 
        --                   mapDirection f x y
        --         mapDir≡' x@(posE , posD) y = {!   !}
                   
                -- path : {x : position (E * D)} → PathP
                --     (λ _ →
                --     direction C (mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩) x) →
                --     direction
                --     (mkpoly (position E) (λ z → direction E z) *
                --      mkpoly (position D) (λ z → direction D z))
                --     x)
                --     (mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩) x) (mapDirection f x)
                -- path = {!   !}
                -- mapDir≡ : (mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩)) ≡ mapDirection f
                -- mapDir≡ = funExt (λ x → path)
                -- helper2 : subst
                --             (λ mapPos →
                --                 (fromPos : position (E * D)) →
                --                 direction C (mapPos fromPos) → direction (E * D) fromPos)
                --             (λ _ → mapPosition (ev ∘ₚ ⟨ curry f × idLens ⟩))
                --             (mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩))
                --             ≡ mapDirection f
                -- helper2 = 
                --    (substRefl 
                --         { B = λ (h : position (E * D) → position C) → (x : position (E * D)) → direction C (h x) → direction (E * D) x}
                --         (mapDirection (ev ∘ₚ ⟨ curry f × idLens ⟩))
                --     ) ∙ mapDir≡
            

                                    

  
          