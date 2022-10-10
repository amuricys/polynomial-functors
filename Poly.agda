module Poly where

open import Relation.Binary.PropositionalEquality

record Polynomial : Set₁ where
    constructor MkPolynomial
    field
        position : Set
        direction : position -> Set

open Polynomial

record Arrow (from to : Polynomial) : Set where
    constructor MkArrow
    field
        mapPosition : position from -> position to
        mapDirection : (fromPos : position from) -> direction to (mapPosition fromPos) -> direction from fromPos

open Arrow

id : {Poly : Polynomial} -> Arrow Poly Poly
id = record { mapPosition = λ z → z ; mapDirection = λ fromPos z → z }

data Either (A B : Set) : Set where
    left : A -> Either A B
    right : B -> Either A B

either : {A B : Set} {X : Set₁} -> Either A B -> (A -> X) -> (B -> X) -> X
either (left x) f g = f x
either (right x) f g = g x

_+_ : Polynomial -> Polynomial -> Polynomial
(MkPolynomial PosA DirA) + (MkPolynomial PosB DirB) = MkPolynomial (Either PosA PosB) (\Pos -> either Pos DirA DirB)

data F : Set where

Zero : Polynomial
Zero = MkPolynomial F (λ ())

test : {x : Set} -> Either F x ≡ x
test = {!   !}


+leftUnit : (Poly : Polynomial) -> Zero + Poly ≡ Poly
+leftUnit (MkPolynomial position direction) = {!   !}

+rightUnit : (Poly : Polynomial) -> Poly + Zero ≡ Poly
+rightUnit (MkPolynomial position direction) = {!   !}

+commutative : (A B : Polynomial) -> A + B ≡ B + A
+commutative = {!   !}

data B : Set where
    true : B
    false : B

testEither : Either B F ≡ F
testEither = {!   !}

hej1 : Either B F -> B
hej1 (left x) = x

hej2 : B -> Either B F
hej2 x = left x


data And (A B : Set) : Set where
    and : A -> B -> And A B

ex : Polynomial
ex = MkPolynomial B (\b -> B)

_*_ : Polynomial -> Polynomial -> Polynomial
A * B = MkPolynomial (And (position A) (position B)) help
    where
        help : (x : And (position A) (position B)) → Set
        help (and x y) = Either (direction A x) (direction B y)

ex2 : Polynomial
ex2 = ex + ex

ex3 : Polynomial
ex3 = ex2 * ex2

ArenaIO : Set -> Set -> Polynomial
ArenaIO Input Output = MkPolynomial Output (λ _ → Input)

-- | S*Y^S
Self : Set -> Polynomial
Self S = ArenaIO S S

-- Zero positions.
Closed : Polynomial
Closed = Self F

data T : Set where
    tt : T

record MooreMachine (State Input Output : Set) : Set where
    constructor MkMooreMachine
    field
        -- initialState : Arrow (Self T) (Self State)
        currentState : State
        arrow : Arrow (Self State) (ArenaIO Input Output)

not : B -> B
not true = false
not false = true

hej : MooreMachine B B B
hej = MkMooreMachine (true) (MkArrow (λ z → not z ) (λ fromPos z → z))

data List (A : Set) : Set where
    nil : List A
    cons : A -> List A -> List A

run : MooreMachine B B B -> B
run (MkMooreMachine initialPos (MkArrow mapPosition₂ mapDirection₂)) = newPos
    where 
        -- initialPos : B
        -- initialPos = mapPosition₁ tt

        theirPos : B
        theirPos = mapPosition₂ initialPos

        newPos : B
        newPos = mapDirection₂ theirPos initialPos

run2 : MooreMachine B B B -> List B -> List B
run2 b nil = nil
run2 (MkMooreMachine currentState arrow) (cons x xs) = cons newState (run2 (MkMooreMachine newState arrow) xs)
    where
        newState : B
        newState = (arrow . mapPosition) currentState

tst = run2 hej (cons true (cons true (cons true nil)))
    
record DFA (State A : Set) : Set where
    constructor MkDFA
    field
        initialState : State 
        arrow : Arrow (Self State) (ArenaIO A B)

data Three : Set where
    one : Three
    two : Three
    three : Three

ex' : DFA Three B
ex' = MkDFA one (MkArrow accept move)
    where
        accept : (x : Three) → B
        accept one = false
        accept two = true
        accept three = false

        move : (x : Three) (x₁ : B) → Three
        move = {!   !}
        
        
-- (MkArrow (λ z → z) (λ fromPos z → z))
-- Moore : {State Input Output : Set} -> 
-- Moore = {!   !}

-- composition 
--- Composition
-- _$_ : {A B C : Polynomial} -> Arrow A B -> Arrow B C -> Arrow A C
-- f $ g = record { mapPosition = λ z → mapPosition g (mapPosition f z) ; mapDirection = λ fromPos x → {!   !} }
-- p2p3 ∙ p1p2 = 
--   Morph (sendOnPosition p2p3 ∘ sendOnPosition p1p2) 
--         (\p1pos -> sendOnDecision p1p2 p1pos ∘ sendOnDecision p2p3 (sendOnPosition p1p2 p1pos) )

-- Lecture1

Ysqr : Polynomial
Ysqr = ArenaIO T B

One : Polynomial
One = ArenaIO T F

TwoY : Polynomial 
TwoY = ArenaIO B T

A : Polynomial
A = Ysqr + (TwoY + One)

-- y^1 + y^2 + y^3 + y^4 + y^5 ... How to represent?

-- How to apply p(1)?
apply : Polynomial -> Set -> Set
apply p x = {!   !}

