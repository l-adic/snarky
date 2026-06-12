-- | High-level circuit compilation and solving.
-- |
-- | - `compile`: interprets a circuit with the builder to extract constraints
-- | - `makeSolver`: creates a witness solver interpreting with the prover
-- |
-- | Both handle public input/output variable allocation (deterministically,
-- | from the initial state's `nextVar`) and constrain the circuit's output
-- | variables to the computed values. Both run directly in `Effect`: the
-- | open advice tail `r` of the circuit is discharged by a caller-supplied
-- | `AdviceHandler r`, and solver failure is an explicit `Either` (the old
-- | `EXCEPT` row and its `liftExceptRow` widening hack are gone).
module Snarky.Backend.Compile
  ( Checker
  , Solver
  , SolverT
  , compile
  , compile'
  , makeSolver
  , makeSolver'
  , runSolver
  ) where

import Prelude

import Data.Array (zip)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Snarky.Backend.Advice (AdviceHandler, noAdvice)
import Snarky.Backend.Assignments as Assignments
import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState, allocVars, finalize, initialBuilderState, runCircuitBuilder)
import Snarky.Backend.Prover (class SolveCircuit, allocAssignments, runCircuitProver)
import Snarky.Circuit.CVar (CVar(..), EvaluationError, Variable, v0)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Circuit.DSL.Monad (class CheckedType, Snarky, assignVars, check, read, runAsProver)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Type.Proxy (Proxy(..))

-- | `compile` with explicit config. `debug: true` records each variable's
-- | label-stack birth context (read by diagnostic error rendering); the
-- | default skips that per-variable work.
compile'
  :: forall @f c c' a b avar bvar aux r
   . CompileCircuit f c c' aux
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => AdviceHandler r
  -> { debug :: Boolean }
  -> Proxy a
  -> Proxy b
  -> Proxy c'
  -> (avar -> Snarky f c' r bvar)
  -> Effect (CircuitBuilderState c aux)
compile' handler { debug } _ _ _ circuit = do
  -- the backend constructs a fresh initial state (incl. mutable parts)
  -- per invocation — initial states are never shared, by construction
  cbs0 <- initialBuilderState <#> _ { debug = debug }
  let
    n = sizeInFields (Proxy @f) (Proxy @a)
    m = sizeInFields (Proxy @f) (Proxy @b)
  Tuple vars cbs1 <- allocVars (n + m) cbs0
  let
    cbs2 = cbs1 { publicInputs = vars }
    { before: avars, after: bvars } = Array.splitAt n vars
    avar = fieldsToVar @f @a (map Var avars)

    prog :: Snarky f c' r Unit
    prog = do
      check avar
      out <- circuit avar
      for_ (zip (varToFields @f @b out) (map Var bvars)) \(Tuple v1 v2) ->
        assertEqual_ v1 v2
  Tuple _ s <- runCircuitBuilder handler cbs2 prog
  pure (finalize s)

compile
  :: forall @f c c' a b avar bvar aux r
   . CompileCircuit f c c' aux
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => AdviceHandler r
  -> Proxy a
  -> Proxy b
  -> Proxy c'
  -> (avar -> Snarky f c' r bvar)
  -> Effect (CircuitBuilderState c aux)
compile handler = compile' handler { debug: false }

-- | Create a solver with an explicit initial prover state.
-- | Useful for enabling debug mode: pass `{ debug: true }`.
makeSolver'
  :: forall f a b c r avar bvar
   . SolveCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => { debug :: Boolean }
  -> Proxy c
  -> (avar -> Snarky f c r bvar)
  -> SolverT f c r a b
makeSolver' { debug } _ circuit = \handler inputs -> do
  let
    n = sizeInFields (Proxy @f) (Proxy @a)
    m = sizeInFields (Proxy @f) (Proxy @b)
  -- The mutable store is owned by THIS invocation (the solver closure is
  -- reused across e.g. QuickCheck trials, so it must not be captured).
  store <- Assignments.fresh
  Tuple vars st1 <- allocAssignments (n + m) (valueToFields inputs)
    { nextVar: v0, assignments: store, debug, labelStack: [] }
  let
    { before: avars, after: bvars } = Array.splitAt n vars
    avar = fieldsToVar @f @a (map Var avars)

    prog :: Snarky f c r bvar
    prog = do
      check avar
      out <- circuit avar
      -- Bind the circuit's output to the preallocated public-output
      -- variables, then constrain them equal — INSIDE the prover, so
      -- backend reductions allocate/assign their intermediates exactly
      -- as the builder did at compile time.
      assignVars bvars (map valueToFields (read @b out))
      for_ (zip (varToFields @f @b out) (map Var bvars)) \(Tuple v1 v2) ->
        assertEqual_ v1 v2
      pure out
  Tuple eOut s <- runCircuitProver handler st1 prog
  case eOut of
    Left e -> pure (Left e)
    Right outVar -> runAsProver handler s.assignments (read outVar) >>= case _ of
      Left e -> pure (Left e)
      Right output -> Assignments.freeze s.assignments <#> (Right <<< Tuple output)

makeSolver
  :: forall f a b c r avar bvar
   . SolveCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Proxy c
  -> (avar -> Snarky f c r bvar)
  -> SolverT f c r a b
makeSolver = makeSolver' { debug: false }

-- | A solver: given a handler for the circuit's advice effects and the
-- | public input, produce the output and frozen assignments — or the
-- | evaluation error that stopped witnessing.
type SolverT :: Type -> Type -> Row (Type -> Type) -> Type -> Type -> Type
type SolverT f c r a b =
  AdviceHandler r -> a -> Effect (Either EvaluationError (Tuple b (Assignments.Frozen f)))

type Solver f c a b = SolverT f c () a b

runSolver
  :: forall f c a b
   . Solver f c a b
  -> a
  -> Effect (Either EvaluationError (Tuple b (Assignments.Frozen f)))
runSolver s = s noAdvice

type Checker f c =
  (Variable -> Either EvaluationError f)
  -> c
  -> Either EvaluationError Boolean
