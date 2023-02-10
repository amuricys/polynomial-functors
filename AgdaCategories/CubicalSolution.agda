-- Big Proof @ Newton Institute
-- 29 June 2017
-- Cambridge, UK
--
--   Andreas Abel, Agda Tutorial
--
-- Part 4: Cubical

-- Requires Agda 2.6.0

{-# OPTIONS --postfix-projections #-}
{-# OPTIONS --cubical #-}

module CubicalSolution where

open import Agda.Primitive public
-- open CubicalPrimitives public

infix 0 _≡_

postulate
  _≡_   : ∀ {a} {A : Set a}      → A    → A    → Set a
  PathP : ∀ {a} (A : I → Set a)  → A i0 → A i1 → Set a

{-# BUILTIN PATH  _≡_   #-}
{-# BUILTIN PATHP PathP #-}

-- primitive
--   Partial : ∀{a} (A : Set a) (φ : I) → Set a
--   Partial A φ = (φ = 1) → A

-- primComp is a primitive

-- primComp : ∀ {a} (A : (i : I) → Set (a i))
--              (φ : I) (u : ∀ i → Partial (A i) φ)
--              (a : A i0) → A i1
-- primComp A i1 u a = u i1 (itIsOne : IsOne i1)
-- primComp A (~i ∨ i) (λ j → [ i=0 → u j , i=1 → t j ]) a (i=0) = u i1


-- If we have an interval-indexed set A, we can cast between any slice,
-- in particular, we can `drive` from start A 0 to end A 1.

drive : ∀ {a : I → Level} (A : (i : I) → Set (a i)) → A i0 → A i1
drive A a = primComp A i0 (λ i → isOneEmpty) a

-- There is a constant path from any x to itself.

refl : ∀{a}{A : Set a} (x : A) → x ≡ x
refl x i = x

-- Substitution is an instance of `drive`.

subst : ∀{a b}{A : Set a}(P : A → Set b) {x y : A} (p : x ≡ y) → P x → P y
subst P p = drive λ i → P (p i)

-- J is also an instance of `drive`.

J : ∀ {a b} {A : Set a} {x : A} (P : (y : A) → x ≡ y → Set b)
      {y : A} (p : x ≡ y) → P x (refl x) → P y p
J P p = drive λ i → P (p i) (λ j → p (primIMin i j))
  -- p : x ≡ y
  -- A i0 = P x (refl x) = P (p i0) (λ j → p i0) = P (p i1) (λ j → p (min j i0))
  -- A i1 = P y p        = P (p i1) (λ j → p j ) = P (p i1) (λ j → p (min j i1))
  -- A i = P (p i) (λ j → p (min j i))

-- Symmetry is by inverting the direction.

sym : ∀{a}{A : Set a} {x y : A} (p : x ≡ y) → y ≡ x
sym p i = p (primINeg i)

-- Transitivity is the usual instance of subst.

trans : ∀{a}{A : Set a} {x y z : A} (p : x ≡ y) (q : y ≡ z) → x ≡ z
trans {x = x} p q = drive (λ i → x ≡ q i) p
  -- ?r i0 = x
  -- ?r i1 = z
  -- p i0 = x
  -- p i1 = y

-- Congruence

cong : ∀ {a b} {A : Set a} {B : Set b} (f : A → B) {x y : A} (p : x ≡ y) → f x ≡ f y
cong f p i = f (p i)

-- Streams

record Stream (A : Set) : Set where
  coinductive
  field  head : A
         tail : Stream A
open Stream

-- Constant stream

repeat : {A : Set} (a : A) → Stream A
repeat a .head = a
repeat a .tail = repeat a

-- Constant stream defined by emitting two elements at time

rep2  : {A : Set} (a : A) → Stream A
rep2 a .head       = a
rep2 a .tail .head = a
rep2 a. tail .tail = rep2 a

-- The two constant streams are equal.

lem : ∀ {A} (a : A) → repeat a ≡ rep2 a
lem a i .head       = a
lem a i .tail .head = a
lem a i .tail .tail = lem a i


-- any function (also over streams) is a congruence

-- map for streams

map : {A B : Set} (f : A → B) (s : Stream A) → Stream B
map f s .head = f (s .head)
map f s .tail = map f (s .tail)

-- iterating a function f from a start value produces a stream

iterate : {A : Set} (f : A → A) (a : A) → Stream A
iterate f a .head = a
iterate f a .tail = iterate f (f a)

-- With composition

infixl 6 _∘_

_∘_ : ∀{A B C : Set} → (B → C) → (A → B) → A → C
g ∘ f = λ x → g (f x)

-- map f can be fused into iterated f
-- map f . iterate f = iterate f . f

map-iterate : ∀{A : Set} (f : A → A) → map f ∘ iterate f ≡ iterate f ∘ f
map-iterate f i a .head = f a
map-iterate f i a .tail = map-iterate f i (f a)
