-- | Witness computation backend.
-- |
-- | `runCircuitProver` interprets the `circuit` effect by computing witness
-- | values: `Exists` RUNS the witness computation against the current
-- | assignments and records the results. Constraints are ignored unless
-- | `debug` is set (they're assumed validated during compilation).
module Snarky.Backend.Prover
  ( runCircuitProver
  , ProverState
  , emptyProverState
  , class SolveCircuit
  , proverConstraint
  , allocAssignments
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable as Foldable
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Run (EFFECT, Run)
import Run as Run
import Snarky.Backend.Assignments (Assignments)
import Snarky.Backend.Assignments as Assignments
import Snarky.Circuit.CVar (EvaluationError(..), Variable, incrementVariable, v0)
import Snarky.Circuit.DSL.Monad (AsProver(..), CIRCUIT, CircuitF(..), _circuit, runAsProver)
import Snarky.Constraint.Basic (class BasicSystem, Basic)
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField)
import Type.Row (type (+))

type ProverState f =
  { nextVar :: Variable
  , assignments :: Assignments f
  , debug :: Boolean
  , labelStack :: Array String
  }

emptyProverState :: forall f. ProverState f
emptyProverState =
  { nextVar: v0
  , assignments: Assignments.emptyFrozen
  , debug: false
  , labelStack: []
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
    | s.debug = pure case Basic.debugCheck (flip Assignments.lookup s.assignments) c of
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

-- | Interpret the `circuit` effect in prover mode over an open tail of advice
-- | effects `r` (witness computations may use them). A witness failure
-- | short-circuits the whole interpretation. Runs at `EFFECT + r`: the
-- | assignment store is mutable, written once per variable as it is
-- | allocated.
runCircuitProver
  :: forall f c r a
   . SolveCircuit f c
  => ProverState f
  -> Run (CIRCUIT f c (EFFECT + r)) a
  -> Run (EFFECT + r) (Tuple (Either EvaluationError a) (ProverState f))
runCircuitProver s0 r0 = tailRecM go (Tuple s0 r0)
  where
  handle = Run.on _circuit Left Right

  -- Stack safety: every interpreter step is a `tailRecM` `Step` in the
  -- target `Run r` (whose `MonadRec` is stack-safe), so circuits with
  -- hundreds of thousands of ops interpret in constant stack.
  go
    :: SolveCircuit f c
    => Tuple (ProverState f) (Run (CIRCUIT f c (EFFECT + r)) a)
    -> Run (EFFECT + r) (Step (Tuple (ProverState f) (Run (CIRCUIT f c (EFFECT + r)) a)) (Tuple (Either EvaluationError a) (ProverState f)))
  go (Tuple s r) = case Run.peel r of
    Left v -> case handle v of
      Left cf -> case cf of
        Fresh k ->
          let
            var = s.nextVar
          in
            pure (Loop (Tuple (s { nextVar = incrementVariable var }) (k var)))
        AddConstraint c k ->
          Run.liftEffect (proverConstraint c s) <#> case _ of
            Right s' -> Loop (Tuple s' k)
            Left e -> Done (Tuple (Left (contextualize s e)) s)
        Exists n w k ->
          runAsProver s.assignments (AsProver w) >>= case _ of
            Left e -> pure (Done (Tuple (Left (contextualize s e)) s))
            Right fields -> Run.liftEffect (allocAssignments n fields s) <#> \(Tuple vs s') ->
              Loop (Tuple s' (k vs))
        Assign vars w k ->
          runAsProver s.assignments (AsProver w) >>= case _ of
            Left e -> pure (Done (Tuple (Left (contextualize s e)) s))
            Right fields -> do
              Run.liftEffect $ Foldable.for_ (Array.zip vars fields) \(Tuple var fv) ->
                Assignments.set var fv s.assignments
              pure (Loop (Tuple s k))
        PushLabel l k ->
          pure (Loop (Tuple (s { labelStack = Array.snoc s.labelStack l }) k))
        PopLabel k ->
          pure (Loop (Tuple (s { labelStack = Array.init s.labelStack # fromMaybe [] }) k))
      Right other ->
        Run.send other <#> \r' -> Loop (Tuple s r')
    Right a ->
      pure (Done (Tuple (Right a) s))
