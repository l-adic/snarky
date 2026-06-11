-- | High-level circuit compilation and solving.
-- |
-- | - `compile`: interprets a circuit with the builder to extract constraints
-- | - `makeSolver`: creates a witness solver interpreting with the prover
-- |
-- | Both handle public input/output variable allocation (deterministically,
-- | from the initial state's `nextVar`) and constrain the circuit's output
-- | variables to the computed values.
module Snarky.Backend.Compile
  ( Checker
  , Solver
  , SolverT
  , liftExceptRow
  , compilePure
  , compile
  , makeSolver
  , makeSolver'
  , runSolver
  , runSolverT
  ) where

import Prelude

import Data.Array (zip)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Map (Map)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Run (EFFECT, Run)
import Run as Run
import Run.Except (EXCEPT)
import Run.Except as Except
import Snarky.Backend.Assignments as Assignments
import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState, allocVars, finalize, runCircuitBuilder)
import Snarky.Backend.Prover (class SolveCircuit, ProverState, allocAssignments, emptyProverState, runCircuitProver)
import Snarky.Circuit.CVar (CVar(..), EvaluationError, Variable)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Circuit.DSL.Monad (class CheckedType, CircuitF(..), Snarky, check, liftCircuit, read, runAsProverPure, runSnarky, unAsProver)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))
import Unsafe.Coerce (unsafeCoerce)

compilePure
  :: forall @f c c' a b avar bvar aux
   . CompileCircuit f c c' aux
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Proxy a
  -> Proxy b
  -> Proxy c'
  -> (avar -> Snarky f c' () bvar)
  -> CircuitBuilderState c aux
  -> CircuitBuilderState c aux
compilePure pa pb pc circuit = Run.extract <<< compile pa pb pc circuit

compile
  :: forall @f c c' a b avar bvar aux r
   . CompileCircuit f c c' aux
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Proxy a
  -> Proxy b
  -> Proxy c'
  -> (avar -> Snarky f c' r bvar)
  -> CircuitBuilderState c aux
  -> Run r (CircuitBuilderState c aux)
compile _ _ _ circuit cbs0 = do
  let
    n = sizeInFields (Proxy @f) (Proxy @a)
    m = sizeInFields (Proxy @f) (Proxy @b)
    Tuple vars cbs1 = allocVars (n + m) cbs0
    cbs2 = cbs1 { publicInputs = vars }
    { before: avars, after: bvars } = Array.splitAt n vars
    avar = fieldsToVar @f @a (map Var avars)

    prog :: Snarky f c' r Unit
    prog = do
      check avar
      out <- circuit avar
      for_ (zip (varToFields @f @b out) (map Var bvars)) \(Tuple v1 v2) ->
        assertEqual_ v1 v2
  Tuple _ s <- runCircuitBuilder cbs2 (runSnarky prog)
  pure (finalize s)

-- | Create a solver with an explicit initial prover state.
-- | Useful for enabling debug mode: pass `emptyProverState { debug = true }`.
makeSolver'
  :: forall f a b c r avar bvar
   . SolveCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => ProverState f
  -> Proxy c
  -> (avar -> Snarky f c (EFFECT + r) bvar)
  -> SolverT f c r a b
makeSolver' initialState _ circuit = \inputs -> do
  let
    n = sizeInFields (Proxy @f) (Proxy @a)
    m = sizeInFields (Proxy @f) (Proxy @b)
  -- The mutable store is owned by THIS invocation (the solver closure is
  -- reused across e.g. QuickCheck trials, so it must not be captured).
  store <- Run.liftEffect Assignments.fresh
  Tuple vars st1 <- Run.liftEffect $ allocAssignments (n + m) (valueToFields inputs)
    (initialState { assignments = store })
  let
    { before: avars, after: bvars } = Array.splitAt n vars
    avar = fieldsToVar @f @a (map Var avars)

    prog :: Snarky f c (EFFECT + r) bvar
    prog = do
      check avar
      out <- circuit avar
      -- Bind the circuit's output to the preallocated public-output
      -- variables, then constrain them equal — INSIDE the prover, so
      -- backend reductions allocate/assign their intermediates exactly
      -- as the builder did at compile time.
      liftCircuit (Assign bvars (map valueToFields (unAsProver (read @b out))) unit)
      for_ (zip (varToFields @f @b out) (map Var bvars)) \(Tuple v1 v2) ->
        assertEqual_ v1 v2
      pure out
  Tuple eOut s <- liftExceptRow (runCircuitProver st1 (runSnarky prog))
  case eOut of
    Left e -> Except.throw e
    Right outVar -> case runAsProverPure (read outVar) s.assignments of
      Left e -> Except.throw e
      Right output -> pure $ Tuple output (Assignments.toMap s.assignments)

makeSolver
  :: forall f a b c r avar bvar
   . SolveCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Proxy c
  -> (avar -> Snarky f c (EFFECT + r) bvar)
  -> SolverT f c r a b
makeSolver = makeSolver' emptyProverState

type SolverT :: Type -> Type -> Row (Type -> Type) -> Type -> Type -> Type
type SolverT f c r a b = a -> Run (EXCEPT EvaluationError + EFFECT + r) (Tuple b (Map Variable f))

runSolverT
  :: forall f c r a b
   . SolverT f c r a b
  -> a
  -> Run (EFFECT + r) (Either EvaluationError (Tuple b (Map Variable f)))
runSolverT f a = Except.runExcept (f a)

type Solver f c a b = SolverT f c () a b

runSolver
  :: forall f c a b
   . Solver f c a b
  -> a
  -> Effect (Either EvaluationError (Tuple b (Map Variable f)))
runSolver c a = Run.runBaseEffect $ runSolverT c a

-- | Widen an open row by the solver's EXCEPT channel. Safe for the same
-- | reason `Run.expand` is (a `Run r` program can never produce an effect
-- | outside `r`); spelled with `unsafeCoerce` because the `Union` solver
-- | cannot align two open tails (`Run.expand` is itself `unsafeCoerce`
-- | behind that unsolvable proof).
liftExceptRow :: forall e r a. Run r a -> Run (EXCEPT e + r) a
liftExceptRow = unsafeCoerce

type Checker f c =
  (Variable -> Either EvaluationError f)
  -> c
  -> Either EvaluationError Boolean
