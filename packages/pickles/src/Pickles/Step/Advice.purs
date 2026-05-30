-- | The Step circuit's private witness data ("advice").
-- |
-- | In OCaml Pickles (`requests.ml` Step module) the Step circuit pulls
-- | this data via `exists ~request:(Req…)` answered by a handler stack.
-- | The PureScript port models it as a plain record (`StepAdvice`)
-- | computed by the prover (`buildStepAdvice`) and passed by value into
-- | `stepMain`, which projects each field inside an `exists` body. There
-- | is no bespoke prover transformer and no advice typeclass on the
-- | witness monad — the witness monad is the caller's own `m`.
-- |
-- | Request → field inventory (step_main.ml):
-- |   Req.App_state                    → publicInput
-- |   Req.Proof_with_datas             → perProofSlotsCarrier
-- |   Req.Wrap_index                   → wrapVerifierIndex
-- |   Req.Unfinalized_proofs           → publicUnfinalizedProofs
-- |   Req.Messages_for_next_wrap_proof → messagesForNextWrapProof (+ dummy hash for padding)
-- |   previous_proof_statements        → prevAppStates
-- |   per-prove ~handler                → sideloadedVKs
-- | plus `kimchiPrevChallenges` (threaded to the kimchi prover).
module Pickles.Step.Advice
  ( StepAdvice(..)
  ) where

import Prelude

import Data.Newtype (class Newtype)
import Data.Vector (Vector)
import Pickles.Field (StepField, WrapField)
import Pickles.Types (PerProofUnfinalized)
import Pickles.VerificationKey (VerificationKey)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (WeierstrassAffinePoint)
import Snarky.Types.Shifted (SplitField, Type2)

newtype StepAdvice
  :: Type -> Int -> Int -> Int -> Type -> Int -> Type -> Type -> Type -> Type
newtype StepAdvice prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier =
  StepAdvice
    { perProofSlotsCarrier :: carrier
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
    -- | Dummy hash value used to pad `messagesForNextWrapProof` from
    -- | `len` to `mpvMax` at solve time (OCaml
    -- | `Reduced_messages_for_next_proof_over_same_field.Wrap.dummy.hash`,
    -- | step_main.ml:368-370).
    , messagesForNextWrapProofDummyHash :: F StepField
    , wrapVerifierIndex ::
        VerificationKey wrapVkChunks (WeierstrassAffinePoint PallasG (F StepField))
    -- | Kimchi-level prev_challenges threaded to
    -- | `pallasCreateProofWithPrev`. One entry per prev slot; each
    -- | entry's `challenges` is sized by `ds` (step IPA rounds).
    , kimchiPrevChallenges ::
        Vector len
          { sgX :: WrapField
          , sgY :: WrapField
          , challenges :: Vector ds StepField
          }
    -- | Heterogeneous per-slot prev statements (shape derived from
    -- | `prevsSpec` by `Pickles.Step.Slots.SlotStatementsCarrier`).
    -- | Mirrors OCaml's `previous_proof_statements`. The rule body reads
    -- | slot-specific values out inside its `exists` calls via the
    -- | deferred getter `stepMain` hands it.
    , prevAppStates :: valCarrier
    -- | Runtime side-loaded VK carrier (shape derived from `prevsSpec` by
    -- | `Pickles.Sideload.Advice.SideloadedVKsCarrier`). PS analog of
    -- | OCaml's per-prove `~handler`.
    , sideloadedVKs :: vkCarrier
    }

derive instance
  Newtype
    (StepAdvice prevsSpec ds dw wrapVkChunks inputVal len carrier valCarrier vkCarrier)
    _
