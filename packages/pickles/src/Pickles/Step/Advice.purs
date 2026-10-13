-- | The step circuit's private witness ("advice"): everything
-- | `stepMain` needs that is not in the public input. Proof-dependent
-- | advice is prepared after the rule returns its proof debt.
module Pickles.Step.Advice
  ( StepAdvice(..)
  , StepAdviceSource
  , SlotProofRequest
  , slotProofRequests
  ) where

import Prelude

import Data.Newtype (class Newtype, unwrap)
import Data.Traversable (traverse)
import Data.Vector (Vector)
import Pickles.Field (StepField, WrapField)
import Pickles.Step.Slots (EncodedPrev)
import Pickles.Step.Types (PerProofWitness)
import Pickles.Types (PerProofUnfinalized, StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.VerificationKey (VerificationKey)
import Snarky.Circuit.DSL (AsProver, F, read, readCVar)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)

-- | The statement and flag returned by the rule, read from its variables.
type SlotProofRequest =
  { statement :: Array StepField
  , mustVerify :: Boolean
  }

-- | The proof debt the rule's returned prevs stand for: per slot, the
-- | statement as the rule returned it and whether its proof must verify.
slotProofRequests
  :: forall r len
   . Vector len EncodedPrev
  -> AsProver StepField r (Vector len SlotProofRequest)
slotProofRequests = traverse \prev -> do
  statement <- traverse (map unwrap <<< readCVar) prev.fields
  mustVerify <- read prev.proofMustVerify
  pure { statement, mustVerify }

-- | Rule inputs are available before proofs. Preparation resolves debt
-- | during the full step solve; later allocations read the resulting advice.
-- | These witness actions are ignored during circuit compilation.
type StepAdviceSource prevsSpec inputVal len valCarrier r =
  { publicInput :: AsProver StepField r inputVal
  , prevAppStates :: AsProver StepField r valCarrier
  , prepare :: Vector len SlotProofRequest -> AsProver StepField r Unit
  , getAdvice ::
      AsProver StepField r
        (StepAdvice prevsSpec StepIPARounds WrapIPARounds WrapVkChunks inputVal len valCarrier)
  }

newtype StepAdvice
  :: Type -> Int -> Int -> Int -> Type -> Int -> Type -> Type
newtype StepAdvice prevsSpec ds dw wrapVkChunks inputVal len valCarrier =
  StepAdvice
    { perProofSlotsCarrier ::
        Vector len
          ( PerProofWitness wrapVkChunks ds dw
              (F StepField)
              (Type2 (SplitField (F StepField) Boolean))
              Boolean
          )
    , publicInput :: inputVal
    , publicUnfinalizedProofs ::
        Vector len
          ( PerProofUnfinalized
              dw
              (Type2 (SplitField (F StepField) Boolean))
              (F StepField)
              Boolean
          )
    , messagesForNextWrapProof :: Vector len (F StepField)
    -- | Pads `messagesForNextWrapProof` from `len` to `mpvMax` at solve
    -- | time.
    , messagesForNextWrapProofDummyHash :: F StepField
    , wrapVerifierIndex ::
        VerificationKey wrapVkChunks (WeierstrassAffinePoint PallasG (F StepField))
    -- | Previous challenges threaded to `pallasCreateProofWithPrev`,
    -- | one entry per prev slot.
    , kimchiPrevChallenges ::
        Vector len
          { sgX :: WrapField
          , sgY :: WrapField
          , challenges :: Vector ds StepField
          }
    -- | The prev statements, one per slot, shaped from `prevsSpec` by
    -- | `Pickles.Step.Slots.SlotStatementsCarrier`. The rule body reads
    -- | slot-specific values out of it through the deferred getter
    -- | `stepMain` hands it.
    , prevAppStates :: valCarrier
    }

derive instance
  Newtype
    (StepAdvice prevsSpec ds dw wrapVkChunks inputVal len valCarrier)
    _
