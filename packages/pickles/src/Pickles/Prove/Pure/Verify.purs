-- | The verifier's counterpart to
-- | `Pickles.Prove.Pure.Wrap.wrapComputeDeferredValues`. Without the
-- | step proof there is no `proofOraclesRec` call to sample the
-- | Fiat–Shamir challenges, only the wrap statement's minimal skeleton
-- | and its `sponge_digest_before_evaluations` checkpoint. So the
-- | sponge is replayed from that checkpoint to recover `xi` and `r`,
-- | and the `Pickles.Prove.Pure.Common` helpers derive the rest.
-- |
-- | On the fields `assembleWrapMainInput` reads, the two must agree.
module Pickles.Prove.Pure.Verify
  ( ExpandDeferredInput
  , expandDeferredForVerify
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Foldable (for_)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.DeferredValues (BranchData, PlonkMinimal, ScalarChallenge)
import Pickles.Field (StepField)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (collapseChunkedEvals)
import Pickles.Prove.Pure.Common (combinedInnerProductBatchChunked, computeBpChalsAndB, derivePlonk, ftEval0)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesOutput)
import Pickles.Sponge (PureSpongeM, absorb, evalPureSpongeM, initialSponge, squeeze, squeezeScalarChallengePure)
import Pickles.Types (ChunkedEvals, StepIPARounds)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.SizedF (SizedF, unwrapF, wrapF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toShifted)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)

type ExpandDeferredInput n =
  { -- Carried (raw) values from the wrap proof's minimal proof state.
    rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField

  -- The inner step proof's data, carried by the wrap proof. Chunked;
  -- `collapseChunkedEvals` below derives the collapsed form once zeta
  -- and zetaw are known, while the combined inner product takes the
  -- chunked form as it is.
  , chunkedEvals :: ChunkedEvals StepField
  , pEval0Chunks :: Array StepField
  , oldBulletproofChallenges :: Vector n (Vector StepIPARounds StepField)

  -- Step domain and SRS metadata, from the step verifier index.
  , domainLog2 :: Int
  , zkRows :: Int
  , srsLengthLog2 :: Int
  , generator :: StepField
  , shifts :: Vector 7 StepField
  , vanishesOnZk :: StepField
  , omegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> StepField
  , endo :: StepField
  , linearizationPoly :: LinearizationPoly StepField
  }

-- | One field element squeezed from a fresh sponge that has absorbed
-- | every expanded previous-proof bp challenge, outer by inner.
challengesDigest
  :: forall n
   . Vector n (Vector StepIPARounds StepField)
  -> StepField
challengesDigest expandedOldBpChals =
  evalPureSpongeM (initialSponge) do
    for_ expandedOldBpChals \inner -> for_ inner absorb
    squeeze

-- | The deferred values recovered from a wrap proof's carried minimal
-- | statement: replay the sponge, then run the carried values through
-- | the `Pickles.Prove.Pure.Common` derivations.
expandDeferredForVerify
  :: forall n
   . ExpandDeferredInput n
  -> WrapDeferredValuesOutput
expandDeferredForVerify input =
  let
    -- Only zeta is expanded here; alpha is expanded below for
    -- `oraclesReconstructed`, and beta and gamma stay raw.
    zetaField = coerce (toFieldPure input.rawPlonk.zeta (F input.endo))

    zetaw = zetaField * input.generator

    -- Collapsed by Horner at `zeta^(2^srsLengthLog2)`, for
    -- `derivePlonk` and `ftEval0`; the combined inner product below
    -- takes the chunked form instead.
    collapsedEvals = collapseChunkedEvals
      { rounds: input.srsLengthLog2
      , zeta: zetaField
      , zetaOmega: zetaw
      }
      input.chunkedEvals

    -- Sponge replay to recover xi and r.
    -- `input.oldBulletproofChallenges` arrives already endo-expanded.
    { xiRawSized, rRawSized } =
      evalPureSpongeM (initialSponge) do
        absorb input.spongeDigestBeforeEvaluations
        absorb (challengesDigest input.oldBulletproofChallenges)
        absorb input.chunkedEvals.ftEval1
        -- Absorption order is fixed by the prover's FrSponge: public
        -- evals, then z, 6 index, 15 witness, 15 coeff, 6 sigma.
        absorbChunked input.chunkedEvals.publicEvals
        absorbChunked input.chunkedEvals.zEvals
        for_ input.chunkedEvals.indexEvals absorbChunked
        for_ input.chunkedEvals.witnessEvals absorbChunked
        for_ input.chunkedEvals.coeffEvals absorbChunked
        for_ input.chunkedEvals.sigmaEvals absorbChunked
        xiChal <- squeezeScalarChallengePureF
        rChal <- squeezeScalarChallengePureF
        pure { xiRawSized: xiChal, rRawSized: rChal }
      where
      -- One polynomial's chunks: all at zeta, then all at zetaw.
      absorbChunked :: NonEmptyArray _ -> _
      absorbChunked chunks = do
        for_ (NEA.toArray chunks) \pe -> absorb pe.zeta
        for_ (NEA.toArray chunks) \pe -> absorb pe.omegaTimesZeta

    xiField = coerce (toFieldPure xiRawSized (F input.endo))

    rField = coerce (toFieldPure rRawSized (F input.endo))

    derivePlonkInput =
      { plonkMinimal: input.rawPlonk
      , w: map _.zeta (Vector.take @7 collapsedEvals.witnessEvals)
      , sigma: map _.zeta collapsedEvals.sigmaEvals
      , zZeta: collapsedEvals.zEvals.zeta
      , zOmegaTimesZeta: collapsedEvals.zEvals.omegaTimesZeta
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      }

    stepPlonkDerived = derivePlonk derivePlonkInput

    ftEval0Input =
      { plonkMinimal: input.rawPlonk
      , allEvals: collapsedEvals
      , pEval0Chunks: input.pEval0Chunks
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      , vanishesOnZk: input.vanishesOnZk
      , omegaForLagrange: input.omegaForLagrange
      , linearizationPoly: input.linearizationPoly
      }

    stepFtEval0 = ftEval0 ftEval0Input

    cipInput =
      { allEvals: input.chunkedEvals
      , publicEvals: input.chunkedEvals.publicEvals
      , ftEval0: stepFtEval0
      , ftEval1: input.chunkedEvals.ftEval1
      , oldBulletproofChallenges: input.oldBulletproofChallenges
      , xi: xiField
      , r: rField
      , zeta: zetaField
      , zetaw
      }

    cipActual = combinedInnerProductBatchChunked cipInput

    newBpResult = computeBpChalsAndB
      { rawPrechallenges: map unwrapF input.rawBulletproofChallenges
      , endo: input.endo
      , zeta: zetaField
      , zetaw
      , r: rField
      }

    -- The verifier can reconstruct every `OraclesResult` field.
    -- `assembleWrapMainInput` reads only a few, but
    -- `WrapDeferredValuesOutput` carries the whole record.
    expandedPlonk =
      { alpha: coerce (toFieldPure input.rawPlonk.alpha (F input.endo)) :: StepField
      , beta: coerce (SizedF.toField input.rawPlonk.beta) :: StepField
      , gamma: coerce (SizedF.toField input.rawPlonk.gamma) :: StepField
      , zeta: zetaField
      }

    oraclesReconstructed =
      { alpha: expandedPlonk.alpha
      , beta: unwrapF input.rawPlonk.beta
      , gamma: unwrapF input.rawPlonk.gamma
      , zeta: zetaField
      , v: xiField
      , u: rField
      , ftEval1: input.chunkedEvals.ftEval1
      , publicEvals:
          { zeta: collapsedEvals.publicEvals.zeta
          , omegaTimesZeta: collapsedEvals.publicEvals.omegaTimesZeta
          }
      , fqDigest: input.spongeDigestBeforeEvaluations
      , alphaChal: unwrapF input.rawPlonk.alpha
      , zetaChal: unwrapF input.rawPlonk.zeta
      , vChal: unwrapF xiRawSized
      , uChal: unwrapF rRawSized
      }
  in
    { plonk: stepPlonkDerived
    , combinedInnerProduct: toShifted (F cipActual)
    , xi: xiRawSized
    , bulletproofPrechallenges: input.rawBulletproofChallenges
    , b: toShifted (F newBpResult.b)
    , branchData: input.branchData
    , xHatEvals:
        { zeta: collapsedEvals.publicEvals.zeta
        , omegaTimesZeta: collapsedEvals.publicEvals.omegaTimesZeta
        }
    , spongeDigestBeforeEvaluations: input.spongeDigestBeforeEvaluations
    , oracles: oraclesReconstructed
    , newBulletproofChallenges: newBpResult
    }

-- | `Pickles.Sponge.squeezeScalarChallengePure` at the
-- | `ScalarChallenge (F StepField)` the deferred values want.
squeezeScalarChallengePureF :: PureSpongeM StepField (SizedF 128 (F StepField))
squeezeScalarChallengePureF = wrapF <$> squeezeScalarChallengePure
