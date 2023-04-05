module ours where

open import Function hiding (Morphism; id)
open import Data.Product
open import Agda.Builtin.Unit
open import Agda.Builtin.Nat
open import Agda.Builtin.Int hiding (pos)


-- NFP: Note for presentation

--- Objects
record Poly : Set₁ where
  constructor PolyConstr
  field 
    pos : Set
    decision : pos → Set

--- Morphisms
open Poly
record Morphism (src : Poly) (tgt : Poly) : Set where
  constructor Morph
  field
    sendOnPosition : pos src → pos tgt
    sendOnDecision : (p : pos src) → decision tgt (sendOnPosition p) → decision src p

open Morphism

--- Identity (NFP: great example of the expressiveness of dependent Sets)
identity : (p : Poly) → Morphism p p
identity p = Morph (λ z → z) (λ p z → z) -- this was AUTO SOLVED and is correct

--- Composition
_∙_ : {p1 p2 p3 : Poly} → Morphism p2 p3 →  Morphism p1 p2  → Morphism p1 p3
p2p3 ∙ p1p2 = 
  Morph (sendOnPosition p2p3 ∘ sendOnPosition p1p2) 
        (\p1pos → sendOnDecision p1p2 p1pos ∘ sendOnDecision p2p3 (sendOnPosition p1p2 p1pos) )


--- Interpretation: Dynamical systems
-- helpers
-- PolyIO : (i : Set) → (o : Set) → Poly --positions as output and
-- PolyIO i o = MkPoly o (\_ → i)           --dectinctions as input

-- Self : Set → Poly
-- Self s = PolyIO s s


-- Sy^S → By^A equipped with
-- update : (A × S) → S
-- readout : S → B
record DynSystem (input : Set) (output : Set) (states : Set) : Set where
  constructor DS
  field
    update : (input × states) → states 
    readout : states → output

record DynSysAsPolyMorphism (input : Set) (output : Set) (states : Set) : Set where
  constructor DSasPoly
  field
    dynamics : Morphism (PolyConstr states (λ _ → states)) (PolyConstr output (λ _ → input))

---- STRAIGHT FROM IDRIS:

-- redefining Stream
record Stream (A : Set) : Set where
  coinductive
  constructor _::_
  field
    hd : A
    tl : Stream A

record DynSystemIdr : Set₁ where
   constructor MkDynSystem
   field
     stateSpace : Set
     interface : Poly -- NFP: "interface" as in "what a user interacting with this DS needs to provide and can expect to receive"
     dynamics : Morphism (PolyConstr stateSpace (\_ → stateSpace)) interface
open DynSystemIdr



Closed : Poly
Closed = PolyConstr ⊤ (\_ → ⊤)

enclose : (aa : Poly) →  Set
enclose a = Morphism a Closed

{-# TERMINATING #-}
run : (d : DynSystemIdr) → enclose (interface d) → (stateSpace d) → Stream (pos (interface d))
run d e s = outp :: (run d e next)
            where
              outp : pos (interface d)
              outp = sendOnPosition (dynamics d) s
              next : stateSpace d
              next = sendOnDecision (dynamics d) s $ sendOnDecision e outp {!   !}


id : {A : Set} → A → A
id x = x

PolyIO : (i : Set) → (o : Set) → Poly -- positions as output and
PolyIO i o = PolyConstr o (\_ → i)       -- distinctions as input

Self : Set → Poly
Self s = PolyIO s s

funcToDynSystem : {s : Set} → {t : Set} → (s → t) → DynSystemIdr
funcToDynSystem {s} {t} f = MkDynSystem t bodyf phenof
  where
    bodyf : Poly
    bodyf = PolyIO s t
    phenof : Morphism (Self t) bodyf
    phenof = Morph id (\_ → f)

_&_ : Poly → Poly → Poly
a & b = PolyConstr posJuxt disJuxt
  where 
    posJuxt : Set
    posJuxt = (pos a × pos b)
    disJuxt : posJuxt → Set
    disJuxt (pa , pb) = (decision a pa × decision b pb)

_&&&_ : DynSystemIdr → DynSystemIdr → DynSystemIdr
_&&&_ dyn1 dyn2 = MkDynSystem state12 body12 pheno12
          where
            state12 : Set
            body12  : Poly
            pheno12 : Morphism (Self state12) body12
            state12 = stateSpace dyn1 × stateSpace dyn2
            body12  = (interface dyn1) & (interface dyn2)
            pheno12 = Morph o i
              where
                o : (stateSpace dyn1 × stateSpace dyn2) → (pos (interface dyn1) × pos (interface dyn2))
                o (s1 , s2) = (sendOnPosition (dynamics dyn1) s1 , sendOnPosition (dynamics dyn2) s2)
                i : (s12 : (stateSpace dyn1 × stateSpace dyn2)) → decision body12 (o s12) → state12 
                i (s1 , s2) (d1 , d2) = 
                  (sendOnDecision (dynamics dyn1) s1 d1 , sendOnDecision (dynamics dyn2) s2 d2)

delay : DynSystemIdr
delay = funcToDynSystem {Nat} {Nat} (\s → s)

plus : DynSystemIdr
plus = funcToDynSystem (uncurry _+_)


Prefib : DynSystemIdr
Prefib = plus &&& delay

Emitter : Set → Poly
Emitter t = PolyConstr ⊤ (\_ → t)

snd : {a b : Set} → (a × b) → b
snd (_ , de) = de

fibwd : Morphism (interface Prefib) (Emitter Nat)
fibwd = Morph sendOnPos {!   !} 
          where
            sendOnPos : (Nat × Nat) → Nat
            sendOnPos (pl , de) = de
            sendOnDec : (p : (Nat × Nat)) → (a : Set) → decision (interface Prefib) p
            sendOnDec (pl , de) _ = ((de , pl) , pl)


-- install : (d : DynSystemIdr) → (a : Poly) → Morphism (interface d) a → DynSystemIdr
-- install d a l = MkDynSystem (stateSpace d) a (l ∘ (dynamics d))

-- encloseFunction : {t u : Set} → (t → u) → Morphism (PolyConstr u (\ _ → t)) (⊤ (\_ → t))
-- encloseFunction {t} {u} f = Morph (\_ → ⊤) (\d → \_ → f d)

-- auto : {m : Set} → enclose (Emitter m)
-- auto {m} = encloseFunction $ \_ → ⊤

-- Fibonacci : DynSystemIdr
-- Fibonacci = install Prefib (Emitter Int) fibwd

-- FibSeq : Stream Int
-- FibSeq = run Fibonacci auto (1 , 1)     