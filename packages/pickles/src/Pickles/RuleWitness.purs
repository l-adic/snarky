-- | Rule allocations observed during the step solve, before backend
-- | reduction. Their final assignments supply the replay witness.
module Pickles.RuleWitness
  ( RuleWitness
  , RuleCapture
  , captureAllocations
  , ruleWitness
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.List (List(..))
import Data.List as List
import Data.Maybe (Maybe(..))
import Data.Traversable (traverse)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Pickles.Field (StepField)
import Snarky.Backend.Assignments as Assignments
import Snarky.Circuit.CVar (EvaluationError(..), Variable)
import Snarky.Circuit.DSL.Monad (CircuitOps(..), Snarky(..))

-- | Input fields and check/body allocations in replay-local order.
type RuleWitness = { input :: Array StepField, values :: Array StepField }

-- | Source allocations, in reverse batch order, including the input.
type RuleCapture = Ref (List (Array Variable))

-- | Observe source allocations while delegating every circuit operation.
-- | Allocations inside backend constraint reduction are not observed.
captureAllocations :: forall f c r a. Maybe RuleCapture -> Snarky f c r a -> Snarky f c r a
captureAllocations Nothing body = body
captureAllocations (Just captured) (Snarky body) = Snarky \(CircuitOps ops) -> do
  let
    save vars = Ref.modify_ (Cons vars) captured $> vars
  body $ CircuitOps ops
    { freshOp = ops.freshOp >>= \v -> save [ v ] $> v
    , existsOp = \n advice -> ops.existsOp n advice >>= save
    }

-- | Read the recorded source variables from the original solve.
ruleWitness
  :: Int
  -> List (Array Variable)
  -> Assignments.Frozen StepField
  -> Either EvaluationError RuleWitness
ruleWitness inputSize batches assignments = do
  let vars = Array.concat (Array.fromFoldable (List.reverse batches))
  if inputSize < 0 || Array.length vars < inputSize then
    Left (FailedAssertion "rule witness: missing input allocations")
  else do
    fields <- traverse
      ( \v -> case Assignments.lookupFrozen v assignments of
          Nothing -> Left (MissingVariable v)
          Just x -> Right x
      )
      vars
    pure { input: Array.take inputSize fields, values: Array.drop inputSize fields }
