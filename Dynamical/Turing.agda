{-# OPTIONS --sized-types #-}

module Dynamical.Turing where

open import Data.Integer
open import Data.Nat hiding (pred ; suc)
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Codata.Stream hiding (_++_)
open import Agda.Builtin.Size
open import Data.List hiding (take)
open import Data.Sum
open import Data.Vec.Functional hiding (take; _++_ ; _∷_ ; [])
open import Data.Vec hiding (take; _++_ ; _∷_ ; [])

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
  constructor mkAction
  field
    write : Alphabet
    move : Movement

actTape : Action → Tape → Tape
actTape (mkAction symbol movement) tape = moveTape movement (writeTape symbol tape)

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

inputTape : List Alphabet → Tape
inputTape [] = blankTape
inputTape (x ∷ xs) = writeTape x (moveTape right (inputTape xs))


bitflipTape : Tape
bitflipTape = inputTape (one  ∷ zero ∷ zero ∷ zero ∷ one ∷ [])

BitflipState : Set
BitflipState = ⊤

processorInterface : Polynomial
processorInterface = myInterface

data Halt : Set where
  halt : Halt

Recipe : Set
Recipe = ℕ → Alphabet → Alphabet × Movement × ℕ ⊎ Halt

bitflipProgram : Recipe
bitflipProgram state zero = inj₁ (one , (right , state))
bitflipProgram state one = inj₁ (zero , (right , state))
bitflipProgram state blank = inj₁ (zero , (right , state)) -- inj₂ halt

bitflipDynamics : Lens (selfMonomial MyState) processorInterface
bitflipDynamics = output ⇆ update
  where
    output : MyState → ProcessorPos
    output (running state prevAction) = running prevAction
    output halted = halted

    update : (fromPos : MyState) → processorDir (output fromPos) → MyState
    update (running currentState x₁) alpha with bitflipProgram currentState alpha
    ... | inj₁ (newAlpha , movement , newState) = running newState (record { write = newAlpha ; move = movement })
    ... | inj₂ halt = halted 
    update halted tt = halted

bitflipSystem : DynamicalSystem
bitflipSystem .state  = MyState
bitflipSystem .interface  = myInterface
bitflipSystem .dynamics  = bitflipDynamics

turingImpl' : DynamicalSystem
turingImpl' = tapeSystem &&& bitflipSystem

turingSystem' : DynamicalSystem
turingSystem' = install turingImpl' turingInterface turingWiring

result' : Codata.Stream.Stream TuringOutput Agda.Builtin.Size.∞
result' = run turingSystem' (unit ⇆ λ _ → unit) (running bitflipTape , running 0 (record { write = one ; move = right }))

result2' = take 4 result

beautify : Codata.Stream.Stream TuringOutput Agda.Builtin.Size.∞ → (List Alphabet) ⊎ ⊤
beautify xs = yo finalOutput
  where
    finalOutput = Data.Vec.last (take 20 xs)

    outputTape : ℕ → Tape → List Alphabet
    outputTape zero tape = []
    outputTape (ℕ.suc n) tape = read tape ∷ (outputTape n (moveTape left tape))

    yo : TuringOutput → (List Alphabet) ⊎ ⊤
    yo (finished x) = inj₁ (outputTape 10 (moveTape left x))
    yo working = inj₂ tt


result2'' = beautify result'



-- -- Things for addition

-- -- Two numbers converted to binary, with blank space as separator
-- additionTape : ℕ → ℕ → Tape
-- additionTape x y = inputTape (xBinary blank++ yBinary)
--   where
--     xBinary : List Alphabet
--     xBinary = one  ∷ zero ∷ [] -- todo

--     yBinary : List Alphabet
--     yBinary = one  ∷ zero ∷ [] -- todo

--     _blank++_ : List Alphabet → List Alphabet → List Alphabet
--     xs blank++ ys = xs ++ (blank ∷ ys)


-- BitflipState : State
-- BitflipState = 

-- flipDynamics : 


-- AdditionState : Set
-- AdditionState = ℕ



-- additionDynamics : Lens (selfMonomial MyState) processorInterface
-- additionDynamics = mapPos ⇆ {!   !}
--   where
--     mapPos : MyState → ProcessorPos
--     mapPos (running nat prevAction) = running prevAction
--     mapPos halted = halted

--     mapDir : (fromPos : MyState) → processorDir (mapPos fromPos) → MyState
--     mapDir (running state prevAction) alpha = {!   !}
--     mapDir halted tt = halted

-- additionSystem : DynamicalSystem
-- additionSystem .state = MyState -- Natural number is not enough, need something else
-- additionSystem .interface = processorInterface
-- additionSystem .dynamics  = additionDynamics


-- ProcessorState : Set
-- ProcessorState = ℕ

-- data Halt : Set where
--   halt : Halt

-- -- currentState, currentSymbel, newSymbol, movement, newState
-- -- Same format as: http://morphett.info/turing/turing.html#LoadMenu
-- Recipe : Set
-- Recipe = ProcessorState → Alphabet → Alphabet × Movement × ProcessorState ⊎ Halt


-- additionRecipe : Recipe
-- additionRecipe 0 blank = inj₁ (blank , (right , 1))
-- additionRecipe 0 x = inj₁ (x , (right , 0))

-- additionRecipe 1 blank = inj₁ (blank , (left , 2))
-- additionRecipe 1 x = inj₁ (x , (right , 1))

-- additionRecipe 2 zero = inj₁ (blank , (left , 3))
-- additionRecipe 2 one = inj₁ (blank , (left , 4))
-- additionRecipe 2 blank = inj₁ (blank , (left , 9))

-- -- 3x
-- additionRecipe 3 blank = inj₁ (blank , (left , 5))
-- additionRecipe 3 x = inj₁ (x , left , 3)

-- -- 3y
-- additionRecipe 4 char = {!   !}

-- -- 4x

-- additionRecipe 5 char = {!   !}
-- -- 4y
-- additionRecipe 6 char = {!   !}
-- additionRecipe 7 char = {!   !}
-- additionRecipe _ _ = {!   !}

-- -- recipe zero alpha = {!   !}
-- -- recipe (ℕ.suc proc) alpha = {!   !}

-- -- record RecipeLine : Set where
-- --   constructor mkRecipeLine
-- --   field
-- --     currentState : ProcessorState
-- --     currentSymbol : Alphabet
-- --     newSymbol : Alphabet
-- --     movement : Movement
-- --     newState : ProcessorState ⊎ Halt

-- -- bake : List RecipeLine → {! Dic  !}
-- -- bake = {!   !}

 
