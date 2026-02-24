-- | Diagnostic utility for circuit debugging.
-- |
-- | Run the same polymorphic circuit through `CircuitDebuggerT` to get precise
-- | error locations when the normal compile+prove pipeline fails.
-- |
-- | ```purescript
-- | -- When circuitSpecPure' fails, diagnose with:
-- | debugCircuitPure (Proxy @(KimchiConstraint f)) circuit failingInput
-- | -- → Left (FailedAssertion "R1CS constraint unsatisfied: ...")
-- | ```
module Test.Snarky.Circuit.Debugger
  ( debugCircuit
  , debugCircuitPure
  , debugCircuitInputs
  , debugCircuitPureInputs
  ) where

import Prelude

import Data.Array (zip)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_, traverse_)
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Snarky.Backend.Builder (class CompileCircuit, CircuitBuilderState)
import Snarky.Backend.Compile (Checker, makeSolver)
import Snarky.Backend.Debugger (class DebugCircuit, CircuitDebuggerT, getAssignments, runCircuitDebuggerT, setAssignments, throwDebuggerError)
import Snarky.Backend.Prover (class SolveCircuit, emptyProverState)
import Snarky.Circuit.CVar (CVar(..), EvaluationError)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM, Snarky, check, fresh, read, runAsProverT, runSnarky)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Curves.Class (class PrimeField)
import Test.Snarky.Circuit.Utils (Expectation, PostCondition, runCircuitSpec)
import Test.QuickCheck (Result(..))
import Test.Spec.Assertions (fail)
import Type.Proxy (Proxy(..))

-- | Run a circuit through `CircuitDebuggerT` for eager constraint checking.
-- |
-- | Mirrors `makeSolver` but evaluates constraints immediately during witness
-- | computation. On failure, returns the exact `EvaluationError` at the point
-- | where the circuit went wrong.
debugCircuit
  :: forall f c m a b avar bvar
   . DebugCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Monad m
  => Proxy c
  -> (forall t. CircuitM f c t m => avar -> Snarky c t m bvar)
  -> a
  -> m (Either EvaluationError b)
debugCircuit _ circuit inputs = do
  eres <- flip runCircuitDebuggerT emptyProverState do
    let n = sizeInFields (Proxy @f) (Proxy @a)
    let m_ = sizeInFields (Proxy @f) (Proxy @b)
    vars <- replicateA (n + m_) fresh
    let { before: avars, after: bvars } = Array.splitAt n vars
    setAssignments $ zip avars (valueToFields inputs)
    outVar <- runSnarky $ do
      let var = fieldsToVar @f @a (map Var avars)
      check @f @c var
      circuit var
    eres <- getAssignments >>= runAsProverT (read outVar)
    case eres of
      Left e -> throwDebuggerError e
      Right output -> do
        setAssignments $ zip bvars (valueToFields output)
        runSnarky $
          for_ (zip (varToFields @f @b outVar) (map Var bvars)) \(Tuple v1 v2) -> do
            assertEqual_ v1 v2 :: Snarky c (CircuitDebuggerT f) m Unit
        pure output
  case eres of
    Tuple (Left e) _ -> pure $ Left e
    Tuple (Right b) _ -> pure $ Right b

-- | Pure variant of `debugCircuit` for circuits with `Identity` base monad.
debugCircuitPure
  :: forall f c a b avar bvar
   . DebugCircuit f c
  => CheckedType f c avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => Proxy c
  -> (forall t. CircuitM f c t Identity => avar -> Snarky c t Identity bvar)
  -> a
  -> Either EvaluationError b
debugCircuitPure pc circuit inputs = un Identity $ debugCircuit pc circuit inputs

-- | Run circuit tests with automatic debugger re-run on failure.
-- |
-- | Same interface as `circuitSpecInputs` but takes the circuit function directly.
-- | On failure, re-runs the failing input through `CircuitDebuggerT` and prints
-- | the labeled error for diagnosis.
debugCircuitInputs
  :: forall f c c' r m a b avar bvar
   . DebugCircuit f c'
  => CompileCircuit f c c' r
  => SolveCircuit f c'
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Show a
  => Monad m
  => (m ~> Effect)
  -> (forall t. CircuitM f c' t m => avar -> Snarky c' t m bvar)
  -> (a -> Expectation b)
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Array a
  -> Aff Unit
debugCircuitInputs nat circuit testFunction checker postCondition builtState inputs =
  let
    spec =
      { builtState
      , checker
      , solver: makeSolver (Proxy @c') circuit
      , testFunction
      , postCondition
      }
    spc = runCircuitSpec spec
  in
    traverse_
      ( \a -> do
          result <- liftEffect $ nat $ spc a
          case result of
            Success -> pure unit
            Failed msg -> do
              debugResult <- liftEffect $ nat $ (debugCircuit (Proxy @c') circuit a :: m (Either EvaluationError b))
              case debugResult of
                Left e ->
                  fail $ "Failed on input " <> show a <> ": " <> msg <> "\n  Debugger: " <> show e
                Right _ ->
                  fail $ "Failed on input " <> show a <> ": " <> msg <> "\n  Debugger: no error (constraint satisfaction or post-condition issue)"
      )
      inputs

-- | Pure variant of `debugCircuitInputs`.
debugCircuitPureInputs
  :: forall f c c' r a b avar bvar
   . DebugCircuit f c'
  => CompileCircuit f c c' r
  => SolveCircuit f c'
  => CheckedType f c' avar
  => CircuitType f a avar
  => CircuitType f b bvar
  => PrimeField f
  => Eq b
  => Show b
  => Show a
  => (forall t. CircuitM f c' t Identity => avar -> Snarky c' t Identity bvar)
  -> (a -> Expectation b)
  -> Checker f c
  -> PostCondition f c r
  -> CircuitBuilderState c r
  -> Array a
  -> Aff Unit
debugCircuitPureInputs circuit testFunction checker postCondition builtState inputs =
  debugCircuitInputs (pure <<< un Identity) circuit testFunction checker postCondition builtState inputs
