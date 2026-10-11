-- | The step circuit's private witness ("advice"): everything
-- | `stepMain` needs that is not in the public input. In the prover,
-- | proof-dependent advice is prepared after the rule returns its obligations;
-- | subsequent witness allocations read that same prepared value.
module Pickles.Step.Advice
  ( StepAdvice(..)
  , StepAdviceSource
  , SlotProofRequest
  ) where

import Data.Newtype (class Newtype)
import Data.Vector (Vector)
import Pickles.Field (StepField, WrapField)
import Pickles.Step.Types (PerProofWitness)
import Pickles.Types (PerProofUnfinalized, StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.VerificationKey (VerificationKey)
import Prelude (Unit)
import Snarky.Circuit.DSL (AsProver, F)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)

-- | The statement and proof obligation actually returned by a rule, read
-- | from its variables after the application witness has been generated.
type SlotProofRequest =
  { statement :: Array StepField
  , mustVerify :: Boolean
  }

-- | Initial rule advice is available before proofs. Preparation runs once,
-- | after the rule, and subsequent allocations share the prepared advice.
-- | All callbacks live in witness computations and are ignored by compilation.
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
