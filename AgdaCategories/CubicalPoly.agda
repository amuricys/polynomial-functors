{-# OPTIONS --cubical #-}

module AgdaCategories.CubicalPoly where

open import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Nat hiding (_+_ ; _*_ )
import Agda.Builtin.Nat
open import Level
open import Categories.Category
import Categories.Object.Initial
open import Categories.Adjoint
open import Categories.Category.Instance.Sets
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
import Cubical.Foundations.Prelude as Cubical
open import Cubical.Data.Sigma.Properties

module StandardDefs where
    data True : Set where
        tt : True
        -- slets gooo
        
    data False : Set where

    data Either A B : Set where
        inL : A -> Either A B
        inR : B -> Either A B

    data And A B : Set where
        and : A -> B -> And A B

    uncurry : {A B C : Set} -> (A -> B -> C) -> (And A B -> C)
    uncurry f (and a b) = f a b

    data List A : Set where
        [] : List A
        _::_ : A -> List A -> List A

    id : {A : Set} -> A -> A
    id x = x

    _∘_ : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
    f ∘ g = λ x -> f (g x)

open StandardDefs

record Polynomial : Set₁ where
    constructor MkPolynomial
    field
        position : Set
        direction : position -> Set

record Arrow (from to : Polynomial) : Set where
    constructor MkArrow
    open Polynomial
    field
        mapPosition : position from -> position to
        mapDirection : (fromPos : position from) -> direction to (mapPosition fromPos) -> direction from fromPos

variable
    A B C D : Polynomial

-- | For each polynomial we have the identity arrow.
-- | Positions are mapped to itself. The direction is taken as itself.
idArrow : Arrow A A
idArrow = MkArrow  id (λ fromPos toDir → toDir) -- Can be autosolved.

compose : Arrow B C -> Arrow A B -> Arrow A C
compose (MkArrow bToCPos cToBDir) (MkArrow aToBPos bToADir) = MkArrow (bToCPos ∘ aToBPos) (λ fromPos z → bToADir fromPos (cToBDir (aToBPos fromPos) z))  -- Can be autosolved.
                                                            -- MkArrow (comp bToCPos aToBPos) (\xPosA -> λ dirC → bToADir xPosA (cToBDir (aToBPos xPosA) dirC))

_*_ : Arrow B C -> Arrow A B -> Arrow A C
_*_ = compose

compose2 : Arrow A B -> Arrow B C -> Arrow A C
compose2 (MkArrow aToBPos bToADir) (MkArrow bToCPos cToBDir) = MkArrow (bToCPos ∘ aToBPos) (λ fromPos z → bToADir fromPos (cToBDir (aToBPos fromPos) z))  -- Can be autosolved.
                                                            -- MkArrow (comp bToCPos aToBPos) (\xPosA -> λ dirC → bToADir xPosA (cToBDir (aToBPos xPosA) dirC))

composeLeftIdentity : (bToC : Arrow B C) -> compose idArrow bToC Eq.≡ bToC
composeLeftIdentity (MkArrow mapPosition mapDirection) = Eq.refl -- Can be autosolved.

composeRightIdentity : (cToB : Arrow C B) -> compose cToB idArrow Eq.≡ cToB
composeRightIdentity (MkArrow mapPosition mapDirection) = Eq.refl -- Can be autosolved.

composeIsAssoc : {f : Arrow A B} {g : Arrow B C} {h : Arrow C D} -> compose h (compose g f) Eq.≡ compose (compose h g) f
composeIsAssoc = Eq.refl -- Can be autosolved.

composeIsAssocCub : ∀ {A B C D} -> {f : Arrow A B} {g : Arrow B C} {h : Arrow C D} -> ((h * g) * f) Cubical.≡ (h * (g * f))
composeIsAssocCub = Cubical.refl -- Can be autosolved.


-- Got from here https://www.cse.chalmers.se/~abela/bigproof17/CubicalSolution.agda
-- trans : ∀{a}{A : Set a} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
-- trans {x = x} p q = drive (λ i → x ≡ q i) p
-- subst B p pa = transport (λ i → B (p i)) pa

transitivity : ∀ {a} {A : Set a} {x y z : A} (p : x Cubical.≡ y) -> (q : y Cubical.≡ z) -> x Cubical.≡ z
transitivity {x = x} p q =  Cubical.transport (λ i → x Cubical.≡ q i) p

transitivity2 : ∀ {a} {A : Set a} {x y z : A} (p : x Cubical.≡ y) -> (q : y Cubical.≡ z) -> x Cubical.≡ z
transitivity2 {x = x} p q =  Cubical.subst (Cubical._≡_ x) q p

-- We want B to be explicit in subst
-- subst : (B : A → Type ℓ') (p : x ≡ y) → B x → B y
-- subst B p pa = transport (λ i → B (p i)) pa

equiv-resp : {A B C : Polynomial} {f h : Arrow B C} {g i : Arrow A B} → f Cubical.≡ h → g Cubical.≡ i → (f * g) Cubical.≡ (h * i)
equiv-resp  p q ii = (p ii) * (q ii)


polyCategory : ∀ {l1 l2 l3 : Level} -> Category (Level.suc Level.zero) Level.zero Level.zero
polyCategory = record
    { Obj = Polynomial
    ; _⇒_ = Arrow
    ; _≈_ = Cubical._≡_
    ; id = idArrow
    ; _∘_ = _*_
    ; assoc = Cubical.refl
    ; sym-assoc = Cubical.refl
    ; identityˡ = Cubical.refl
    ; identityʳ = Cubical.refl
    ; identity² = Cubical.refl
    ; equiv = record { refl = Cubical.refl ; sym = Cubical.sym ; trans = transitivity2 }
    ; ∘-resp-≈ = equiv-resp
    }

-- ∀ {X Y Z} {f : X -> Y} {g : Y -> Z} →
--   D [ F₁ (C [ g ∘ f ]) ≈ D [ F₁ g ∘ F₁ f ] ]
-- constHomomorph : {X Y Z : Set} {f : X → Y} {g : Y → Z} → 
--   MkArrow (λ x → g (f x)) (λ fromPos ()) 
--   Cubical.≡ 
--   MkArrow (λ x → g (f x)) (λ fromPos z → (λ ()) ((λ ()) z))
-- constHomomorph {f = f} {g = g} i = MkArrow (g ∘ f) (λ fromPos ())

impfunExt2 : {A B : Set} {f g : A → B} →
           ({x : A} → f x Cubical.≡ g x) → f Cubical.≡ g
impfunExt2 p i x = p {x} i

-- identity     : ∀ {A} → D [ F₁ (C.id {A}) ≈ D.id ]
-- homomorphism : ∀ {X Y Z} {f : C [ X , Y ]} {g : C [ Y , Z ]} →
--                     D [ F₁ (C [ g ∘ f ]) ≈ D [ F₁ g ∘ F₁ f ] ]
-- F-resp-≈     : ∀ {A B} {f g : C [ A , B ]} → C [ f ≈ g ] → D [ F₁ f ≈ F₁ g ]

-- Functor sending a set A to the constant polynomial Ay^0 = A
constantPolynomial : Functor (Sets Level.zero) polyCategory
constantPolynomial = record
    { F₀ = λ x → MkPolynomial x λ _ → False
    ; F₁ = λ f → MkArrow (λ x → f x) λ fromPos ()
    ; identity = λ i → MkArrow id λ fromPos x → {!   !}
    ; homomorphism = \{x y z} {f g} i -> MkArrow (g ∘ f) (λ fromPos ())
    ; F-resp-≈ = λ {A B} {f g} p i → MkArrow (impfunExt2 {A = A} {B = B} {f = f} {g = g} {!   !} {!   !}) (λ fromPos ())
    }

-- -- Functor sending a polynomial the zero set "plugging in 0"
-- plugIn0 : Functor polyCategory (Sets Level.zero)
-- plugIn0 = record
--     { F₀ = λ _ -> False
--     ; F₁ = λ f ()
--     ; identity = {!   !}
--     ; homomorphism = {!   !}
--     ; F-resp-≈ = {!   !}
--     }

-- -- The two above are adjoints
-- polyAdjoint : Adjoint constantPolynomial plugIn0
-- polyAdjoint = record 
--     { unit = {!   !}
--     ; counit = {!   !}
--     ; zig = {!   !}
--     ; zag = {!   !} }

-- -- Functor sending a polynomial to its set of positions "plugging in 1"
-- plugIn1 : Functor polyCategory (Sets Level.zero)
-- plugIn1 = record
--     { F₀ = Polynomial.position
--     ; F₁ = Arrow.mapPosition
--     ; identity = {!   !}
--     ; homomorphism = {!   !}
--     ; F-resp-≈ = {!   !}
--     }

-- -- The two above are adjoints "in the other direction"; i.e. plugIn1 is a RIGHT adjoint to constantPolynomial,
-- -- which itself is a left adjoint to plugIn0
-- polyAdjoint2 : Adjoint plugIn1 constantPolynomial
-- polyAdjoint2 = record 
--     { unit = {!   !}
--     ; counit = {!   !}
--     ; zig = {!   !}
--     ; zag = {!   !} }

-- -- Functor sending a set A to the linear polynomial Ay^1 = Ay
-- linearPolynomial : Functor (Sets Level.zero) Poly
-- linearPolynomial = record
--     { F₀ = λ x → MkPolynomial x λ _ → True
--     ; F₁ = λ f → MkArrow f \ _ _ -> tt
--     ; identity = {!   !}
--     ; homomorphism = {!   !}
--     ; F-resp-≈ = {!   !}
--     }

-- polyAdjoint3 : Adjoint linearPolynomial plugIn1
-- polyAdjoint3 = record 
--     { unit = {!   !}
--     ; counit = {!   !}
--     ; zig = {!   !}
--     ; zag = {!   !} }


-- isSetRing : (R : Ring ℓ) → isSet ⟨ P ⟩
-- isSetRing R = R .snd .RingStr.isRing .IsRing.·IsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set

-- groupHom : (G : Group) (H : Group) → Set (Level.zero)
-- groupHom G H = Σ[ f ∈ (G .fst → H .fst) ] IsGroupHom (G .snd) f (H .snd)
-- 
-- isSetGroupHom : isSet (groupHom G H)
-- isSetGroupHom {G = G} {H = H} =
--   isSetΣ (isSetΠ λ _ → is-set (snd H)) λ _ → isProp→isSet (isPropIsGroupHom G H)


-- isSetPolyArrow : (x y : Polynomial) -> isSet (Arrow x y)
-- isSetPolyArrow (MkPolynomial position₁ direction₁) (MkPolynomial position₂ direction₂) = λ x y x₁ y₁ i i₁ → {! !}


-- Now to some (monoidal) operators on polynomials.

-- Sum between two polynomials.
-- Sum of positions. Use either direction of first position or second position.
_+_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA + MkPolynomial posB dirB = MkPolynomial (Either posA posB) (λ {(inL posA) → dirA posA
                                                                                    ; (inR posB) → dirB posB})

-- Unit for sum is 0. 0 positions.
Zero : Polynomial
Zero = MkPolynomial False (λ ())

open Categories.Object.Initial polyCategory

arrowFromZero : {p : Polynomial} -> Arrow Zero p
arrowFromZero {p} = MkArrow (λ ()) (λ ())

module A where
    open Arrow public


-- mEq :  ∀{l}{A B : Container {l}}{f g : A ⇒ B}
--     →  mSh f ≅ mSh g
--     →  (λ {s} → mPos f {s}) ≅ (λ {s} → mPos g {s})
--     →  f ≅ g
-- mEq refl refl = refl

data ℕ : Cubical.Type where
    zeroo : ℕ
    succ : ℕ -> ℕ

elm : {P : ℕ -> Cubical.Type} -> P zeroo -> ((n : ℕ) -> P n -> P (succ n)) -> (n : ℕ) -> P n
elm p0 psuc zeroo = p0
elm p0 psuc (succ n) = psuc n (elm p0 psuc n)



arrowEqual : {f g : Arrow A B}
    -> (A.mapPosition f) Cubical.≡ (A.mapPosition g)
    -- → A.
    -> g Cubical.≡ f
arrowEqual p1 = {!  !}
    -- -> (s : ?) -> A.mapDirection f s Cubical.≡ A.mapDirection g s
    -- -> (λ (s : Polynomial.position A)
    --      -> (Arrow.mapDirection f (Arrow.mapPosition f s) Cubical.≡ (Arrow.mapDirection g (Arrow.mapPosition g s))))
        --  -> (Arrow.mapDirection f (Arrow.mapPosition f s) Cubical.≡ (Arrow.mapDirection g (Arrow.mapPosition g s))))
arrowEqual2 : {f g : Arrow A B}
    -> (A.mapPosition f) Cubical.≡ (A.mapPosition g)
    -- -> (λ {s} -> A.mapDirection f s) Cubical.≡ (λ {s} -> A.mapDirection g s)
    -- -> {! A.mapDirection f Cubical.≡ A.mapDirection g  !}
    -> g Cubical.≡ f
arrowEqual2 p1 p2 = {!  !}

-- applyArrow : {B : Polynomial} -> (A : Polynomial) -> Arrow A B -> A
-- applyArrow a f = {!   !}

-- f : {A : Cubical.Type} -> False -> A
-- f ()

-- g : {A : Cubical.Type} -> False -> A
-- g ()


-- hej2 : {A : Cubical.Type} (a : False) -> f a Cubical.≡ g a
-- hej2 ()

-- hej : {A : Cubical.Type} -> f {A} Cubical.≡ g
-- hej = Cubical.funExt hej2

fromFalseFunctionsEqual : {A : Cubical.Type} (f : False -> A) -> (g : False -> A) -> f Cubical.≡ g
fromFalseFunctionsEqual f g = Cubical.funExt λ {()}

zeroArrowUnique : (f : Arrow Zero A) -> arrowFromZero Cubical.≡ f
zeroArrowUnique f = arrowEqual helper
    where
        helper : A.mapPosition f Cubical.≡ A.mapPosition arrowFromZero
        helper = fromFalseFunctionsEqual (A.mapPosition f) (A.mapPosition arrowFromZero)

-- zeroMapPositionsUnique : {A : Polynomial} (f : Arrow Zero A) -> A.mapPosition f Cubical.≡ (A.mapPosition (arrowFromZero {p = A}) ) -- arrowFromZero
-- zeroMapPositionsUnique {A = A} (MkArrow mapPosition mapDirection) = hej mapPosition (Arrow.mapPosition arrowFromZero)

-- zeroArrowUnique : (f : Arrow Zero A) -> arrowFromZero Cubical.≡ f
-- zeroArrowUnique {A = A} f@(MkArrow mapPosition mapDirection) = {! arrowEqual {A = Zero} {B = A} { f = arrowFromZero} {g = f} (zeroMapPositionsUnique f) !} -- arrowEqual {A = Zero} {B = A} { f = arrowFromZero} {g = f} (?)  -- {! arrowEqual (zeroMapPositionsUnique ? ?) !} -- {! arrowEqual {f = arrowFromZero} {g = f} zeroMapPositionsUnique arrowFromZero f !}

isInitial : IsInitial Zero 
isInitial = record { ! = arrowFromZero ; !-unique = zeroArrowUnique }



-- Product between two polynomials.
-- Pair of position. Each pair of positions has one direction, either from the left or the right polynomial.
_×_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA × MkPolynomial posB dirB = MkPolynomial (And posA posB) \{(and posA posB) → Either (dirA posA) (dirB posB)}

-- Unit for product is 1. 1 position with 0 direction.
One : Polynomial
One = MkPolynomial True (λ _ → False)

-- Tensor between two polynomials. Parallel product.
-- Pair of position. Each pair of position has one direction for each component.
_⊗_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA ⊗ MkPolynomial posB dirB = MkPolynomial (And posA posB) (λ {(and posA posB) → And (dirA posA) (dirB posB)})

-- Unit for tensor is Y. 1 position with 1 direction.
Y : Polynomial
Y = MkPolynomial True (λ _ → True)

-- Composition of polynomials (composition of polynomial functors, which happen to be new polynomial functor!).
_◂_ : Polynomial -> Polynomial -> Polynomial
MkPolynomial posA dirA ◂ MkPolynomial posB dirB = MkPolynomial ((i : posA) -> (dirA i) -> posB) (λ pos → (p : posA) -> (d : dirA p) -> dirB (pos p d))

-- Unit for composition is also Y.
Identity : Polynomial
Identity = Y

compositePower : Polynomial -> Nat -> Polynomial
compositePower p zero = Identity
compositePower p (suc n) = p ◂ (compositePower p n) 

monomial : (A B : Set) -> Polynomial -- A*Y^B
monomial A B = MkPolynomial A (λ _ → B)

selfMonomial : Set -> Polynomial -- S*Y^S
selfMonomial S = monomial S S 

-- Creating dynamical systems.
record DynamicalSystem : Set₁ where
    constructor MkDynamicalSystem
    field
        state : Set -- S
        interface : Polynomial -- p
        dynamics : Arrow (selfMonomial state) interface -- S*Y^S -> p

functionToDynamicalSystem : (A B : Set) -> (A -> B) -> DynamicalSystem
functionToDynamicalSystem A B f = MkDynamicalSystem B (monomial B A) (MkArrow StandardDefs.id (\_ -> f))

delay : (A : Set) -> DynamicalSystem
delay A = functionToDynamicalSystem A A StandardDefs.id

plus : DynamicalSystem
plus = functionToDynamicalSystem (And Nat Nat) Nat (uncurry Agda.Builtin.Nat._+_)

_&&&_ : DynamicalSystem -> DynamicalSystem -> DynamicalSystem
MkDynamicalSystem stateA interfaceA dynamicsA &&& MkDynamicalSystem stateB interfaceB dynamicsB 
    = MkDynamicalSystem (And stateA stateB) (interfaceA ⊗ interfaceB) (MkArrow mapPosition mapDirection)
        where
            mapPosition : (And stateA stateB) → Polynomial.position (interfaceA ⊗ interfaceB)
            mapPosition (and stateA stateB) = and (Arrow.mapPosition dynamicsA stateA) (Arrow.mapPosition dynamicsB stateB)
            mapDirection : (state : (And stateA stateB)) -> Polynomial.direction (interfaceA ⊗ interfaceB) (mapPosition state) -> And stateA stateB
            mapDirection (and sA sB) (and dirA dirB) = and (Arrow.mapDirection dynamicsA sA dirA) (Arrow.mapDirection dynamicsB sB dirB)

prefib : DynamicalSystem
prefib = plus &&& delay Nat

Emitter : Set -> Polynomial
Emitter t = monomial t True

fibwd : Arrow (DynamicalSystem.interface prefib) (Emitter Nat)
fibwd = MkArrow (λ {(and pl de) → de}) (λ {(and pl de) l → and (and de pl) pl })

install : (d : DynamicalSystem) -> (a : Polynomial) -> Arrow (DynamicalSystem.interface d) a -> DynamicalSystem
install d a l = MkDynamicalSystem (DynamicalSystem.state d) a (compose l (DynamicalSystem.dynamics d))

fibonacci : DynamicalSystem
fibonacci = install prefib (Emitter Nat) fibwd

encloseFunction : {t u : Set} -> (t -> u) -> Arrow (monomial t u) Y
encloseFunction f = MkArrow (λ _ → tt) (λ fromPos _ → f fromPos)

enclose : Polynomial -> Set
enclose P = Arrow P Y

auto : {m : Set} -> enclose (Emitter m)
auto = encloseFunction λ _ → tt

record Stream (A : Set) : Set where
    coinductive
    field
        head : A
        tail : Stream A

{-# TERMINATING #-}
run : (d : DynamicalSystem) -> enclose (DynamicalSystem.interface d) -> DynamicalSystem.state d -> Stream (Polynomial.position (DynamicalSystem.interface d))
run d e s = record { head = output ; tail = run d e next }
    where
        output : Polynomial.position (DynamicalSystem.interface d)
        output = (Arrow.mapPosition (DynamicalSystem.dynamics d) s)
        next : DynamicalSystem.state d
        next = Arrow.mapDirection (DynamicalSystem.dynamics d) s (Arrow.mapDirection e output tt)


FibSeq : Stream Nat
FibSeq = run fibonacci auto (and 1 1)

take : {A : Set} -> Nat -> Stream A -> List A
take zero stream =  [] 
take (suc n) stream =  (Stream.head stream) :: (take n (Stream.tail stream))

last : List Nat -> Nat
last [] = 0
last (x :: []) = x
last (x :: xs) = last xs

fibList : List Nat
fibList = take 50 FibSeq


       