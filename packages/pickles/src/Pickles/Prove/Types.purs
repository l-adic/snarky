-- | Types shared by compilation and proof fulfillment.
module Pickles.Prove.Types
  ( ProveError
  , StepInputs
  , BranchProver(..)
  ) where

import Data.Either (Either)
import Effect (Effect)
import Pickles.Types (ApplicationStatement)
import Pickles.Verify (CompiledProof)
import Snarky.Backend.Advice (AdviceHandler)
import Snarky.Circuit.CVar (EvaluationError)

type ProveError = EvaluationError

type StepInputs :: Type -> Type -> Type -> Type
type StepInputs prevsSpec inputVal prevsCarrier =
  { appInput :: inputVal
  -- | One entry per slot, in slot order: a `ProofRef` for a compiled
  -- | slot, a `SideLoadedPrev` for a side-loaded one.
  , prevs :: prevsCarrier
  }

-- | The prover for one branch. A call runs the full step and wrap and
-- | returns the completed proof, including the application's output.
newtype BranchProver
  :: Type -> Int -> Type -> Type -> Type -> Row (Type -> Type) -> Type
newtype BranchProver prevsSpec mpv prevsCarrier inputVal outputVal r =
  BranchProver
    ( AdviceHandler r
      -> StepInputs prevsSpec inputVal prevsCarrier
      -> Effect (Either ProveError (CompiledProof mpv (ApplicationStatement inputVal outputVal)))
    )
