-- | Witness computation backend.
-- |
-- | `runCircuitProver` interprets the `circuit` effect by computing witness
-- | values: `Exists` RUNS the witness computation against the current
-- | assignments and records the results. Constraints are ignored unless
-- | `debug` is set (they're assumed validated during compilation).
module Snarky.Backend.Prover
  ( runCircuitProver
  , ProverState
  , class SolveCircuit
  , proverConstraint
  , allocAssignments
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable as Foldable
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Run (Run)
import Run as Run
import Snarky.Backend.Advice (AdviceHandler(..))
import Snarky.Backend.Assignments (Assignments)
import Snarky.Backend.Assignments as Assignments
import Snarky.Circuit.CVar (EvaluationError(..), Variable, incrementVariable)
import Snarky.Circuit.DSL.Monad (AsProver(..), CIRCUIT, CircuitF(..), _circuit, _effect, runAsProver)
import Snarky.Constraint.Basic (class BasicSystem, Basic)
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)

type ProverState f =
  { nextVar :: Variable
  , assignments :: Assignments f
  , debug :: Boolean
  , labelStack :: Array String
  }

-- | How a backend handles an emitted constraint in prover mode: a transform
-- | of the prover state in `Effect` (backends like kimchi ALLOCATE and
-- | ASSIGN variables in the mutable store while reducing constraints),
-- | failing with an evaluation error. Replaces the old
-- | `ConstraintM (ProverT f)` instances.
class BasicSystem f c <= SolveCircuit f c | c -> f where
  proverConstraint :: c -> ProverState f -> Effect (Either EvaluationError (ProverState f))

-- | `Basic` constraints do no prover-side work; in debug mode they are
-- | checked against the current assignments for rich error messages.
instance PrimeField f => SolveCircuit f (Basic f) where
  proverConstraint c s
    | s.debug = do
        lookupFn <- Assignments.toLookup s.assignments
        pure case Basic.debugCheck lookupFn c of
          Nothing -> Right s
          Just e -> Left e
    | otherwise = pure (Right s)

-- | Allocate `n` consecutive variables and assign them the given values
-- | (writing into the state's mutable store).
allocAssignments
  :: forall f
   . Int
  -> Array f
  -> ProverState f
  -> Effect (Tuple (Array Variable) (ProverState f))
allocAssignments n values s0 = go 0 s0 []
  where
  go i s acc
    | i >= n = pure (Tuple acc s)
    | otherwise = do
        let
          v = s.nextVar
          s' = s { nextVar = incrementVariable v }
        case Array.index values i of
          Just f -> Assignments.set v f s.assignments
          Nothing -> pure unit
        go (i + 1) s' (Array.snoc acc v)

-- | Wrap an error with the current label context (debug mode only), matching
-- | the old `WithLabel (ProverT f)` behavior.
contextualize :: forall f. ProverState f -> EvaluationError -> EvaluationError
contextualize s e
  | s.debug = Array.foldr WithContext e s.labelStack
  | otherwise = e

-- | Interpret the `circuit` effect in prover mode, directly in `Effect`.
-- | The open tail of advice effects `r` (which witness computations may
-- | use) is delegated to the caller's handler — the SAME handler serves
-- | both the circuit row here and the witness row inside `Exists`/`Assign`
-- | (via `runAsProver`). A witness failure short-circuits the whole
-- | interpretation.
runCircuitProver
  :: forall f c r a
   . SolveCircuit f c
  => AdviceHandler r
  -> ProverState f
  -> Run (CIRCUIT f c r) a
  -> Effect (Tuple (Either EvaluationError a) (ProverState f))
runCircuitProver h@(AdviceHandler handler) s0 r0 = tailRecM go (Tuple s0 r0)
  where
  handle = Run.on _circuit Left Right

  -- Stack safety: every interpreter step is a `tailRecM` `Step` in
  -- `Effect` (whose `MonadRec` is a JS loop), so circuits with hundreds
  -- of thousands of ops interpret in constant stack.
  go
    :: SolveCircuit f c
    => Tuple (ProverState f) (Run (CIRCUIT f c r) a)
    -> Effect (Step (Tuple (ProverState f) (Run (CIRCUIT f c r) a)) (Tuple (Either EvaluationError a) (ProverState f)))
  go (Tuple s r) = case Run.peel r of
    Left v -> case handle v of
      Left cf -> case cf of
        Fresh k ->
          let
            var = s.nextVar
          in
            pure (Loop (Tuple (s { nextVar = incrementVariable var }) (k var)))
        AddConstraint c k ->
          proverConstraint c s <#> case _ of
            Right s' -> Loop (Tuple s' k)
            Left e -> Done (Tuple (Left (contextualize s e)) s)
        Exists n w k ->
          runAsProver h s.assignments (AsProver w) >>= case _ of
            Left e -> pure (Done (Tuple (Left (contextualize s e)) s))
            Right fields -> allocAssignments n fields s <#> \(Tuple vs s') ->
              Loop (Tuple s' (k vs))
        Assign vars w k ->
          runAsProver h s.assignments (AsProver w) >>= case _ of
            Left e -> pure (Done (Tuple (Left (contextualize s e)) s))
            Right fields -> do
              Foldable.for_ (Array.zip vars fields) \(Tuple var fv) ->
                Assignments.set var fv s.assignments
              pure (Loop (Tuple s k))
        PushLabel l k ->
          pure (Loop (Tuple (s { labelStack = Array.snoc s.labelStack l }) k))
        PopLabel k ->
          pure (Loop (Tuple (s { labelStack = Array.init s.labelStack # fromMaybe [] }) k))
      Right v' ->
        v' # Run.on _effect (\eff -> eff <#> \r' -> Loop (Tuple s r'))
          (\other -> handler other <#> \r' -> Loop (Tuple s r'))
    Right a ->
      pure (Done (Tuple (Right a) s))
