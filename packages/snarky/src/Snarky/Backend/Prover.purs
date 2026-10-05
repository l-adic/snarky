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
  , checkConstraint
  , allocAssignments
  ) where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Array as Array
import Data.Either (Either(..), note)
import Data.Foldable as Foldable
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Ref as Ref
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Backend.Assignments (Assignments)
import Snarky.Backend.Assignments as Assignments
import Snarky.Circuit.CVar (AffineExpression, EvaluationError(..), Variable, evalAffineExpression, incrementVariable)
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
  -- | The compiled circuit's internal variables with their expressions,
  -- | in increasing order, and how many of them the variable counter has
  -- | passed.
  , internals :: Array (Tuple Variable (AffineExpression f))
  , internalsPassed :: Int
  }

-- | A backend's check of one constraint against the assignments, run in
-- | debug mode for its error message: `Nothing` when the constraint holds.
class BasicSystem f c <= SolveCircuit f c | c -> f where
  checkConstraint :: (Variable -> Maybe f) -> c -> Maybe EvaluationError

instance PrimeField f => SolveCircuit f (Basic f) where
  checkConstraint = Basic.debugCheck

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

-- | Whether the variable counter stands on an internal variable.
atInternal :: forall f. ProverState f -> Boolean
atInternal s = case Array.index s.internals s.internalsPassed of
  Just (Tuple var _) -> var == s.nextVar
  Nothing -> false

-- | Move the variable counter past the internal variables it stands on,
-- | assigning each the value of its expression. The compile gave them
-- | these ids, and an expression mentions only smaller ones.
passInternals :: forall f. PrimeField f => ProverState f -> Effect (ProverState f)
passInternals = tailRecM \s -> case Array.index s.internals s.internalsPassed of
  Just (Tuple var expr) | var == s.nextVar ->
    case evalAffineExpression expr (\v -> note (MissingVariable v) (Assignments.lookup v s.assignments)) of
      Left e -> throwEvalError e
      Right a -> Assignments.set var a s.assignments $>
        Loop s { nextVar = incrementVariable var, internalsPassed = s.internalsPassed + 1 }
  _ -> pure (Done s)

-- | Wrap an error with the current label context (debug mode only), matching
-- | the old `WithLabel (ProverT f)` behavior.
contextualize :: forall f. ProverState f -> EvaluationError -> EvaluationError
contextualize s e
  | s.debug = Array.foldr WithContext e s.labelStack
  | otherwise = e

-- | Interpret a circuit in prover mode: run witness computations against
-- | the live assignments, recording results, and compute the compiled
-- | circuit's internal variables as the variable counter reaches them;
-- | constraints are only checked, in debug mode. The SAME advice handler
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
  ea <- catchEvalError do
    a <- g (proverOps advice ref)
    -- The last constraints' internal variables, which no allocation follows.
    Ref.read ref >>= passInternals >>= flip Ref.write ref
    pure a
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
      s <- atFreeVar
      Ref.write (s { nextVar = incrementVariable s.nextVar }) ref
      pure s.nextVar
  , addConstraintOp: \c -> do
      s <- Ref.read ref
      -- `if`, not `when`: its argument would be built for every constraint.
      if s.debug then do
        lookup <- Assignments.toLookup s.assignments
        Foldable.for_ (checkConstraint lookup c) (throwEvalError <<< contextualize s)
      else pure unit
  , existsOp: \n w -> do
      s <- atFreeVar
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
  -- The state, its variable counter moved past any internal variables.
  atFreeVar :: Effect (ProverState f)
  atFreeVar = do
    s <- Ref.read ref
    if atInternal s then passInternals s else pure s

  -- In debug mode, witness failures are wrapped with the label context at
  -- the point of failure (rethrown; recovered at the interpreter boundary).
  runWitness :: ProverState f -> AsProver f r (Array f) -> Effect (Array f)
  runWitness s (AsProver g)
    | s.debug =
        catchEvalError (g (AsProverCtx { assignments: s.assignments, advice })) >>= case _ of
          Left e -> throwEvalError (contextualize s e)
          Right fields -> pure fields
    | otherwise = g (AsProverCtx { assignments: s.assignments, advice })
