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
  ) where

import Prelude

import Data.Array (zip)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..))
import Data.Unfoldable (replicateA)
import Snarky.Backend.Debugger (class DebugCircuit, CircuitDebuggerT, getAssignments, runCircuitDebuggerT, setAssignments, throwDebuggerError)
import Snarky.Backend.Prover (emptyProverState)
import Snarky.Circuit.CVar (CVar(..), EvaluationError)
import Snarky.Circuit.DSL.Assert (assertEqual_)
import Snarky.Circuit.DSL.Monad (class CheckedType, class CircuitM, class WithLabel, Snarky, check, fresh, read, runAsProverT, runSnarky)
import Snarky.Circuit.Types (class CircuitType, fieldsToVar, sizeInFields, valueToFields, varToFields)
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
  -> (forall t. CircuitM f c t m => WithLabel t => avar -> Snarky c t m bvar)
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
  -> (forall t. CircuitM f c t Identity => WithLabel t => avar -> Snarky c t Identity bvar)
  -> a
  -> Either EvaluationError b
debugCircuitPure pc circuit inputs = un Identity $ debugCircuit pc circuit inputs
