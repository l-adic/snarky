-- | The step circuit's private witness ("advice"): everything
-- | `stepMain` needs that is not in the public input. Built by
-- | `buildStepAdvice` and passed by value; `stepMain` projects each
-- | field inside its own `exists` body.
module Pickles.Step.Advice
  ( StepAdvice(..)
  ) where

import Data.Newtype (class Newtype)
import Data.Vector (Vector)
import Pickles.Field (StepField, WrapField)
import Pickles.Step.Types (PerProofWitness)
import Pickles.Types (PerProofUnfinalized)
import Pickles.VerificationKey (VerificationKey)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)

newtype StepAdvice
  :: Type -> Int -> Int -> Int -> Type -> Int -> Type -> Type -> Type
newtype StepAdvice prevsSpec ds dw wrapVkChunks inputVal len valCarrier vkCarrier =
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
    -- | The runtime side-loaded VKs, shaped from `prevsSpec` by
    -- | `Pickles.Sideload.Advice.SideloadedVKsCarrier`.
    , sideloadedVKs :: vkCarrier
    }

derive instance
  Newtype
    (StepAdvice prevsSpec ds dw wrapVkChunks inputVal len valCarrier vkCarrier)
    _
