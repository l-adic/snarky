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
import Effect.Ref as Ref
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Backend.Assignments (Assignments)
import Snarky.Backend.Assignments as Assignments
import Snarky.Circuit.CVar (EvaluationError(..), Variable, incrementVariable)
import Snarky.Circuit.DSL.Monad (AsProver(..), AsProverCtx(..), CircuitOps(..), Snarky(..))
import Snarky.Circuit.EvalError (catchEvalError, throwEvalError)
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

-- | Interpret a circuit in prover mode: run witness computations against
-- | the live assignments, recording results; constraints do backend-
-- | specific prover work (`proverConstraint`). The SAME advice handler
-- | serves every witness computation. A failing witness or constraint
-- | throws (`Snarky.Circuit.EvalError`); this boundary recovers it as
-- | `Either`, alongside the final prover state.
runCircuitProver
  :: forall f c r a
   . SolveCircuit f c
  => AdviceHandler r
  -> ProverState f
  -> Snarky f c r a
  -> Effect (Tuple (Either EvaluationError a) (ProverState f))
runCircuitProver advice s0 (Snarky g) = do
  ref <- Ref.new s0
  ea <- catchEvalError (g (proverOps advice ref))
  s <- Ref.read ref
  pure (Tuple ea s)

-- | The prover's operations over a mutable state cell.
proverOps
  :: forall f c r
   . SolveCircuit f c
  => AdviceHandler r
  -> Ref.Ref (ProverState f)
  -> CircuitOps f c r
proverOps advice ref = CircuitOps
  { freshOp: do
      s <- Ref.read ref
      Ref.write (s { nextVar = incrementVariable s.nextVar }) ref
      pure s.nextVar
  , addConstraintOp: \c -> do
      s <- Ref.read ref
      proverConstraint c s >>= case _ of
        Right s' -> Ref.write s' ref
        Left e -> throwEvalError (contextualize s e)
  , existsOp: \n w -> do
      s <- Ref.read ref
      fields <- runWitness s w
      Tuple vs s' <- allocAssignments n fields s
      Ref.write s' ref
      pure vs
  , assignOp: \vars w -> do
      s <- Ref.read ref
      fields <- runWitness s w
      Foldable.for_ (Array.zip vars fields) \(Tuple var fv) ->
        Assignments.set var fv s.assignments
  , pushLabelOp: \l -> Ref.modify_ (\s -> s { labelStack = Array.snoc s.labelStack l }) ref
  , popLabelOp: Ref.modify_ (\s -> s { labelStack = Array.init s.labelStack # fromMaybe [] }) ref
  }
  where
  -- In debug mode, witness failures are wrapped with the label context at
  -- the point of failure (rethrown; recovered at the interpreter boundary).
  runWitness :: ProverState f -> AsProver f r (Array f) -> Effect (Array f)
  runWitness s (AsProver g)
    | s.debug =
        catchEvalError (g (AsProverCtx { assignments: s.assignments, advice })) >>= case _ of
          Left e -> throwEvalError (contextualize s e)
          Right fields -> pure fields
    | otherwise = g (AsProverCtx { assignments: s.assignments, advice })
