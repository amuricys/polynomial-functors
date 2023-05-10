{-# OPTIONS --sized-types #-}

module Dynamical.Turing where

open import Data.Integer
open import Data.Nat hiding (pred ; suc)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Codata.Stream
open import Agda.Builtin.Size

open import CategoryData.Everything
open import Dynamical.System
open DynamicalSystem

data Alphabet : Set where
  zero : Alphabet
  one : Alphabet
  blank : Alphabet

Tape : Set
Tape = ℤ → Alphabet

blankTape : Tape
blankTape _ = blank

read : Tape → Alphabet
read tape = tape 0ℤ

isZero : ℤ → Bool
isZero (+_ zero) = true
isZero +[1+ n ] = false
isZero (-[1+_] n) = false

writeTape : Alphabet → Tape → Tape
writeTape alpha tape = λ index → if isZero index then alpha else tape index

data Movement : Set where
  left : Movement
  right : Movement

moveTape : Movement → Tape → Tape
moveTape left tape = λ index → tape (pred index)
moveTape right tape = λ index → tape (suc index)

data TapeState : Set where
  running : Tape → TapeState
  halted : Tape → TapeState

data TapePos : Set where
  running : Alphabet → TapePos
  halted : Tape → TapePos

record Action : Set where
  field
    write : Alphabet
    move : Movement

actTape : Action → Tape → Tape
actTape record { write = symbol ; move = movement } tape = moveTape movement (writeTape symbol tape)

data Instruction : Set where
  act : Action → Instruction
  halt : Instruction

tapeDir : TapePos → Set
tapeDir (running alpha) = Instruction
tapeDir (halted tape) = ⊤

tapeInterface : Polynomial
tapeInterface = mkpoly TapePos tapeDir

tapeDynamics : Lens (selfMonomial TapeState) tapeInterface
tapeDynamics = output ⇆ updateState
  where
    output : TapeState → TapePos
    output (running tape) = running (read tape)
    output (halted tape) = halted tape

    updateState : (fromPos : TapeState) → tapeDir (output fromPos) → TapeState
    updateState (running tape) (act action) = running (actTape action tape)
    updateState (running tape) halt = halted tape
    updateState (halted tape) tt = halted tape

tapeSystem : DynamicalSystem
tapeSystem .state = TapeState
tapeSystem .interface = tapeInterface
tapeSystem .dynamics = tapeDynamics

data MyState : Set where
  running : ℕ → Action → MyState
  halted : MyState

data ProcessorPos : Set where
  running : Action → ProcessorPos
  halted : ProcessorPos

processorDir : ProcessorPos → Set
processorDir (running _) = Alphabet
processorDir halted = ⊤ 

myInterface : Polynomial
myInterface = mkpoly ProcessorPos processorDir

myDynamics : Lens (selfMonomial MyState) myInterface
myDynamics = out ⇆ update
  where
    out : MyState → ProcessorPos
    out (running state action) = running action -- Action must be saved.
    out halted = halted

    update : (fromPos : MyState) → processorDir (out fromPos) → MyState
    update (running zero _) _ = running 1 (record { write = one ; move = right })
    update (running (ℕ.suc _) _) _ = halted
    update halted tt = halted

myProgram : DynamicalSystem
myProgram .state = MyState
myProgram .interface = myInterface
myProgram .dynamics = myDynamics

turingImpl : DynamicalSystem
turingImpl = tapeSystem &&& myProgram

data TuringOutput : Set where
  finished : Tape → TuringOutput
  working : TuringOutput

turingInterface : Polynomial
turingInterface = linear TuringOutput

turingWiring : Lens (interface turingImpl) turingInterface
turingWiring = mapPos ⇆ mapDir
  where
    mapPos : position (interface turingImpl) → position turingInterface
    mapPos (running _ , _) = working
    mapPos (halted tape , _) = finished tape

    mapDir : (fromPos : position (interface turingImpl)) → direction turingInterface (mapPos fromPos) → direction (interface turingImpl) fromPos
    mapDir (running alpha , running action) tt = act action , alpha
    mapDir (running x , halted) tt = halt , tt -- bad case
    mapDir (halted x , running x₁) tt = tt , zero -- bad case
    mapDir (halted x , halted) tt = tt , tt

turingSystem : DynamicalSystem
turingSystem = install turingImpl turingInterface turingWiring

unit : {A : Set} → A → ⊤
unit _ = tt

result : Codata.Stream.Stream TuringOutput Agda.Builtin.Size.∞
result = run turingSystem (unit ⇆ λ _ → unit) (running blankTape , running 0 (record { write = blank ; move = left }))

result2 = take 4 result
