-- | Types shared by compilation and proof fulfillment.
module Pickles.Prove.Types
  ( ProveError
  , StepInputs
  , SlotProofDemand
  , BranchProver(..)
  ) where

import Data.Either (Either)
import Effect (Effect)
import Pickles.Field (StepField, WrapField)
import Pickles.Types (ApplicationStatement)
import Pickles.Verify (CompiledProof)
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.CVar (EvaluationError)
import Snarky.Curves.Pasta (PallasG)

type ProveError = EvaluationError

type StepInputs :: Type -> Type -> Type -> Type
type StepInputs prevsSpec inputVal prevsCarrier =
  { appInput :: inputVal
  -- | One entry per slot, in slot order: a `ProofRef` for a compiled
  -- | slot, a `SideLoadedPrev` for a side-loaded one.
  , prevs :: prevsCarrier
  }

-- | What identifies the proof a slot will demand: the wrap verification
-- | key of the slot's source, the statement as the rule returned it, and
-- | whether the solve will demand it at all.
type SlotProofDemand =
  { wrapVK :: VerifierIndex PallasG WrapField
  , statement :: Array StepField
  , mustVerify :: Boolean
  }

-- | The prover for one branch. `prove` runs the full step and wrap and
-- | returns the completed proof, including the application's output.
-- | `demands` is its pre-flight: for the same inputs, what `prepare`
-- | will ask of each slot, in slot order, read from the rule body alone.
-- | The rule's slot count is not among this type's parameters, so the
-- | result is an array rather than a sized vector.
newtype BranchProver
  :: Type -> Int -> Type -> Type -> Type -> Row (Type -> Type) -> Type
newtype BranchProver prevsSpec mpv prevsCarrier inputVal outputVal r =
  BranchProver
    { prove ::
        AdviceHandler r
        -> StepInputs prevsSpec inputVal prevsCarrier
        -> Effect (Either ProveError (CompiledProof mpv (ApplicationStatement inputVal outputVal)))
    , demands ::
        AdviceHandler r
        -> StepInputs prevsSpec inputVal prevsCarrier
        -> Effect (Either EvaluationError (Array SlotProofDemand))
    }
