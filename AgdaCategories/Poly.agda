module AgdaCategories.Poly where

open import Relation.Binary.PropositionalEquality as Eq
open import Agda.Builtin.Nat hiding (_+_ ; _*_ )
import Agda.Builtin.Nat
open import Level
open import Categories.Category

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

composeIsAssoc : {f : Arrow A B} {g : Arrow B C} {h : Arrow C D} -> h * (g * f) Eq.≡ (h * g) * f
composeIsAssoc = Eq.refl -- Can be autosolved.


-- We want B to be explicit in subst
-- subst : (B : A → Type ℓ') (p : x ≡ y) → B x → B y
-- subst B p pa = transport (λ i → B (p i)) pa

equiv-resp : {A B C : Polynomial} {f h : Arrow B C} {g i : Arrow A B} → f ≡ h → g ≡ i → (f * g) ≡ (h * i)
equiv-resp {f = f} {h = h} {g = g} {i = i} p q = {!  !}

polyCategory : ∀ {l1 l2 l3 : Level} -> Category (Level.suc Level.zero) Level.zero Level.zero
polyCategory = record
    { Obj = Polynomial
    ; _⇒_ = Arrow
    ; _≈_ = _≡_
    ; id = idArrow
    ; _∘_ = _*_
    ; assoc = refl
    ; sym-assoc = refl
    ; identityˡ = refl
    ; identityʳ = refl
    ; identity² = refl
    ; equiv = record { refl = refl ; sym = sym ; trans = trans }
    ; ∘-resp-≈ = equiv-resp
    }


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


     