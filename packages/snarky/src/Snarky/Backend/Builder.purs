-- | Circuit compilation backend.
-- |
-- | `runCircuitBuilder` interprets the `circuit` effect by collecting
-- | constraints without computing witness values: `Exists` allocates fresh
-- | variables and DISCARDS the witness computation. Used during compilation
-- | to extract the constraint system structure.
module Snarky.Backend.Builder
  ( initialState
  , runCircuitBuilder
  , execCircuitBuilder
  , CircuitBuilderState
  , class CompileCircuit
  , appendBuilderConstraint
  , finalize
  , Labeled
  , labeled
  , unlabel
  , context
  , Constraints
  , emptyConstraints
  , snocConstraint
  , appendConstraintsBatch
  , constraintsToArray
  , allocVars
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldl) as F
import Data.List (List(..), reverse) as L
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Tuple (Tuple(..))
import Run (Run)
import Run as Run
import Snarky.Circuit.CVar (Variable, incrementVariable, v0)
import Snarky.Circuit.DSL.Monad (CIRCUIT, CircuitF(..), _circuit)
import Snarky.Constraint.Basic (class BasicSystem, Basic)
import Snarky.Curves.Class (class PrimeField)

type Labeled c =
  { constraint :: c
  , context :: Array String
  }

labeled :: forall c. Array String -> c -> Labeled c
labeled ctx c = { constraint: c, context: ctx }

unlabel :: forall c. Labeled c -> c
unlabel = _.constraint

-- | Append-efficient constraint accumulator.
-- |
-- | Stored as a `List` in **reverse** emission order (newest first), so
-- | a single append is O(1) `Cons` (with tail sharing — PureScript
-- | linked lists share structure, unlike `Array` whose every
-- | `snoc`/`cons` does a full `slice()` copy → O(n²) over a build).
-- | Materialised to a forward-order `Array` exactly once at the end
-- | via `constraintsToArray` (O(m)). The observable constraint order
-- | is identical to the old `Array.snoc` accumulation.
newtype Constraints c = Constraints (L.List (Labeled c))

emptyConstraints :: forall c. Constraints c
emptyConstraints = Constraints L.Nil

-- | O(1) single append (to the logical end of the sequence).
snocConstraint :: forall c. Labeled c -> Constraints c -> Constraints c
snocConstraint x (Constraints xs) = Constraints (L.Cons x xs)

-- | Append a batch to the logical end, preserving the batch's own
-- | order. O(|batch|) — touches only the new elements, never copies
-- | the accumulated prefix. Equivalent to `acc <> batch` on the
-- | materialised arrays.
appendConstraintsBatch
  :: forall c. Array (Labeled c) -> Constraints c -> Constraints c
appendConstraintsBatch batch (Constraints xs) =
  Constraints (F.foldl (\acc x -> L.Cons x acc) xs batch)

-- | Materialise to forward (emission) order. O(m), once.
constraintsToArray :: forall c. Constraints c -> Array (Labeled c)
constraintsToArray (Constraints xs) = Array.fromFoldable (L.reverse xs)

context :: forall c. Labeled c -> Array String
context = _.context

type CircuitBuilderState c aux =
  { nextVar :: Variable
  , constraints :: Constraints c
  , publicInputs :: Array Variable
  , aux :: aux
  , labelStack :: Array String
  , varMetadata :: Map Variable (Array String)
  }

-- | How a backend stores an emitted constraint `c'` in a builder state over
-- | stored constraint type `c` (+ backend aux state), and finalizes the state
-- | after the build. Replaces the old `ConstraintM`/`Finalizer`/
-- | `CompileCircuit` class triple.
class BasicSystem f c' <= CompileCircuit f c c' aux | f c -> c', c -> f where
  appendBuilderConstraint :: c' -> CircuitBuilderState c aux -> CircuitBuilderState c aux
  finalize :: CircuitBuilderState c aux -> CircuitBuilderState c aux

instance PrimeField f => CompileCircuit f (Basic f) (Basic f) aux where
  appendBuilderConstraint c s =
    s { constraints = snocConstraint { constraint: c, context: s.labelStack } s.constraints }
  finalize = identity

initialState :: forall c. CircuitBuilderState c Unit
initialState =
  { nextVar: v0
  , constraints: emptyConstraints
  , publicInputs: mempty
  , aux: unit
  , labelStack: []
  , varMetadata: Map.empty
  }

-- | Allocate `n` consecutive variables in a builder state (recording the
-- | current label stack as each variable's metadata, exactly like a fresh
-- | allocation inside the interpreter).
allocVars
  :: forall c aux
   . Int
  -> CircuitBuilderState c aux
  -> Tuple (Array Variable) (CircuitBuilderState c aux)
allocVars n s0 = go 0 s0 []
  where
  go i s acc
    | i >= n = Tuple acc s
    | otherwise =
        let
          v = s.nextVar
        in
          go (i + 1)
            ( s
                { nextVar = incrementVariable v
                , varMetadata = Map.insert v s.labelStack s.varMetadata
                }
            )
            (Array.snoc acc v)

-- | Interpret the `circuit` effect in builder mode over an open tail of
-- | advice effects `r` (which never fire — witness computations are
-- | discarded).
runCircuitBuilder
  :: forall f c c' aux r a
   . CompileCircuit f c c' aux
  => CircuitBuilderState c aux
  -> Run (CIRCUIT f c' r) a
  -> Run r (Tuple a (CircuitBuilderState c aux))
runCircuitBuilder s0 r0 = tailRecM go (Tuple s0 r0)
  where
  handle = Run.on _circuit Left Right

  -- Stack safety: every interpreter step is a `tailRecM` `Step` in the
  -- target `Run r` (whose `MonadRec` is stack-safe), so circuits with
  -- hundreds of thousands of ops interpret in constant stack.
  go
    :: CompileCircuit f c c' aux
    => Tuple (CircuitBuilderState c aux) (Run (CIRCUIT f c' r) a)
    -> Run r (Step (Tuple (CircuitBuilderState c aux) (Run (CIRCUIT f c' r) a)) (Tuple a (CircuitBuilderState c aux)))
  go (Tuple s r) = case Run.peel r of
    Left v -> case handle v of
      Left cf -> case cf of
        Fresh k ->
          let
            Tuple vs s' = allocVars 1 s
          in
            pure (Loop (Tuple s' (k (fromMaybe s.nextVar (Array.head vs)))))
        AddConstraint c k ->
          pure (Loop (Tuple (appendBuilderConstraint c s) k))
        Exists n _ k ->
          let
            Tuple vs s' = allocVars n s
          in
            pure (Loop (Tuple s' (k vs)))
        Assign _ _ k ->
          pure (Loop (Tuple s k))
        PushLabel l k ->
          pure (Loop (Tuple (s { labelStack = Array.snoc s.labelStack l }) k))
        PopLabel k ->
          pure (Loop (Tuple (s { labelStack = Array.init s.labelStack # fromMaybe [] }) k))
      Right other ->
        Run.send other <#> \r' -> Loop (Tuple s r')
    Right a ->
      pure (Done (Tuple a s))

execCircuitBuilder
  :: forall f c c' aux r a
   . CompileCircuit f c c' aux
  => CircuitBuilderState c aux
  -> Run (CIRCUIT f c' r) a
  -> Run r (CircuitBuilderState c aux)
execCircuitBuilder s = map (\(Tuple _ s') -> s') <<< runCircuitBuilder s
