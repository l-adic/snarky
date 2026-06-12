-- | Circuit compilation backend.
-- |
-- | `runCircuitBuilder` interprets the `circuit` effect by collecting
-- | constraints without computing witness values: `Exists` allocates fresh
-- | variables and DISCARDS the witness computation. Used during compilation
-- | to extract the constraint system structure.
module Snarky.Backend.Builder
  ( emptyBuilderState
  , initialBuilderState
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

import Data.Array as Array
import Data.Foldable (foldl) as F
import Data.List (List(..), reverse) as L
import Data.Maybe (fromMaybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Ref as Ref
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Backend.Assignments (Assignments)
import Snarky.Backend.Assignments as Assignments
import Snarky.Circuit.CVar (Variable, incrementVariable, v0)
import Snarky.Circuit.DSL.Monad (CircuitOps(..), Snarky(..))
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
  , debug :: Boolean
  , varMetadata :: Assignments (Array String)
  }

-- | How a backend stores an emitted constraint `c'` in a builder state over
-- | stored constraint type `c` (+ backend aux state), and finalizes the state
-- | after the build. Replaces the old `ConstraintM`/`Finalizer`/
-- | `CompileCircuit` class triple.
class BasicSystem f c' <= CompileCircuit f c c' aux | f c -> c' aux, c' -> c, c -> f where
  appendBuilderConstraint :: c' -> CircuitBuilderState c aux -> Effect (CircuitBuilderState c aux)
  finalize :: CircuitBuilderState c aux -> CircuitBuilderState c aux
  -- | The backend's initial builder state, constructed fresh (including
  -- | all mutable parts) per `compile` invocation — initial states are
  -- | never shared, by construction.
  initialBuilderState :: Effect (CircuitBuilderState c aux)

instance PrimeField f => CompileCircuit f (Basic f) (Basic f) Unit where
  appendBuilderConstraint c s =
    pure s { constraints = snocConstraint { constraint: c, context: s.labelStack } s.constraints }
  finalize = identity
  initialBuilderState = emptyBuilderState unit

-- | Fresh builder state over any aux value (helper for
-- | `initialBuilderState` instances).
emptyBuilderState :: forall c aux. aux -> Effect (CircuitBuilderState c aux)
emptyBuilderState aux = do
  varMetadata <- Assignments.fresh
  pure
    { nextVar: v0
    , constraints: emptyConstraints
    , publicInputs: mempty
    , aux
    , labelStack: []
    , debug: false
    , varMetadata
    }

-- | Allocate `n` consecutive variables in a builder state. In debug mode
-- | the current label stack is recorded as each variable's metadata (read
-- | only by diagnostic error rendering); production builds skip the write.
allocVars
  :: forall c aux
   . Int
  -> CircuitBuilderState c aux
  -> Effect (Tuple (Array Variable) (CircuitBuilderState c aux))
allocVars n s0 = go 0 s0 []
  where
  go i s acc
    | i >= n = pure (Tuple acc s)
    | otherwise = do
        let v = s.nextVar
        when s.debug $ Assignments.set v s.labelStack s.varMetadata
        go (i + 1) (s { nextVar = incrementVariable v }) (Array.snoc acc v)

-- | Interpret a circuit in builder mode: collect constraints, allocate
-- | variables, DISCARD witness computations. The advice handler is unused —
-- | in direct style, advice is only reachable from witness computations,
-- | which the builder never runs — but the parameter is kept so compile and
-- | solve share a calling convention.
runCircuitBuilder
  :: forall f c c' aux r a
   . CompileCircuit f c c' aux
  => AdviceHandler r
  -> CircuitBuilderState c aux
  -> Snarky f c' r a
  -> Effect (Tuple a (CircuitBuilderState c aux))
runCircuitBuilder _ s0 (Snarky g) = do
  ref <- Ref.new s0
  a <- g (builderOps ref)
  s <- Ref.read ref
  pure (Tuple a s)

-- | The builder's operations over a mutable state cell.
builderOps
  :: forall f c c' aux r
   . CompileCircuit f c c' aux
  => Ref.Ref (CircuitBuilderState c aux)
  -> CircuitOps f c' r
builderOps ref = CircuitOps
  { freshOp: do
      s <- Ref.read ref
      Tuple vs s' <- allocVars 1 s
      Ref.write s' ref
      pure (fromMaybe s.nextVar (Array.head vs))
  , addConstraintOp: \c -> do
      s <- Ref.read ref
      s' <- appendBuilderConstraint c s
      Ref.write s' ref
  , existsOp: \n _ -> do
      s <- Ref.read ref
      Tuple vs s' <- allocVars n s
      Ref.write s' ref
      pure vs
  , assignOp: \_ _ -> pure unit
  , pushLabelOp: \l -> Ref.modify_ (\s -> s { labelStack = Array.snoc s.labelStack l }) ref
  , popLabelOp: Ref.modify_ (\s -> s { labelStack = Array.init s.labelStack # fromMaybe [] }) ref
  }

execCircuitBuilder
  :: forall f c c' aux r a
   . CompileCircuit f c c' aux
  => AdviceHandler r
  -> CircuitBuilderState c aux
  -> Snarky f c' r a
  -> Effect (CircuitBuilderState c aux)
execCircuitBuilder h s = map (\(Tuple _ s') -> s') <<< runCircuitBuilder h s
