-- | Verifier-side deferred-values expansion: pure PS port of OCaml
-- | `mina/src/lib/crypto/pickles/wrap_deferred_values.ml:17-193`
-- | `Wrap_deferred_values.expand_deferred`.
-- |
-- | This is the companion of `Pickles.Prove.Pure.Wrap.wrapComputeDeferredValues`,
-- | which is the PROVER side (takes a step proof + calls `pallasProofOracles`
-- | to sample the Fiat–Shamir challenges). The verifier cannot call
-- | `pallasProofOracles` because it doesn't have the step proof — the
-- | carried wrap statement only contains the MINIMAL skeleton plus the
-- | `sponge_digest_before_evaluations` checkpoint. This module replays the
-- | sponge from that checkpoint to recover `xi` and `r`, pulls the raw
-- | 128-bit `alpha / beta / gamma / zeta` directly from the minimal
-- | statement, and reuses the same helpers in `Pickles.Prove.Pure.Common`
-- | to derive `plonk / combined_inner_product / b / bulletproof_challenges`.
-- |
-- | Self-consistency: for any step proof, `expandDeferredForVerify` should
-- | produce the same `WrapDeferredValuesOutput` as `wrapComputeDeferredValues`
-- | would on the fields consumed by `assembleWrapMainInput`. That's the test.
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
import Pickles.Field (StepField)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (ChunkedAllEvals)
import Pickles.PlonkChecks.Chunks as Chunks
import Pickles.Prove.Pure.Common (combinedInnerProductBatchChunked, computeBpChalsAndB, derivePlonk, ftEval0)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesOutput)
import Pickles.Sponge (PureSpongeM, absorb, evalPureSpongeM, initialSponge, squeeze, squeezeScalarChallengePure)
import Pickles.Types (StepIPARounds)
import Pickles.Verify.Types (BranchData, PlonkMinimal, ScalarChallenge)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.SizedF (SizedF, unwrapF, wrapF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (toShifted)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)

-- | Verifier-side input to `expandDeferredForVerify`. The fields split into
-- | three groups:
-- |
-- | * **Carried from wrap statement skeleton.** These come out of the wrap
-- |   proof's `proof_state` unchanged and are just passed through:
-- |   `rawPlonk`, `rawBulletproofChallenges`, `branchData`,
-- |   `spongeDigestBeforeEvaluations`.
-- | * **Prev proofs.** `oldBulletproofChallenges` (from
-- |   `messages_for_next_step_proof.old_bulletproof_challenges`). The
-- |   `allEvals` record (from the wrap proof's carried `prev_evals`, = the
-- |   inner step proof's polynomial evaluations).
-- | * **Static domain / SRS metadata.** Shared with the prover — read from
-- |   the step verifier index at runtime: `domainLog2`, `zkRows`,
-- |   `srsLengthLog2`, `generator`, `shifts`, `vanishesOnZk`,
-- |   `omegaForLagrange`, `endo` (= `endoScalar @StepField`),
-- |   `linearizationPoly`.
type ExpandDeferredInput n =
  { -- Carried (raw) values from the wrap proof's minimal proof state.
    rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField

  -- Evals + prev-proof bp chals (= the inner step proof's data, carried
  -- by the wrap proof). Chunked form (`NonEmptyArray (PointEval f)`
  -- per polynomial); collapsed form derived internally via
  -- `collapseChunkedAllEvals` once zeta/zetaw are known. CIP consumes
  -- chunked directly via `combinedInnerProductBatchChunked`.
  , chunkedAllEvals :: ChunkedAllEvals StepField
  , pEval0Chunks :: Array StepField
  , oldBulletproofChallenges :: Vector n (Vector StepIPARounds StepField)

  -- Static step-domain / SRS metadata (same source as prover — read from
  -- the step verifier index).
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

-- | Compute `challenges_digest = sponge(expanded old_bp_chals flattened)`.
-- | Matches the sub-sponge in `wrap_deferred_values.ml:128-137` — a fresh
-- | `Tick_field_sponge.Field` that absorbs every expanded bp-challenge
-- | (outer × inner), then squeezes one field element.
challengesDigest
  :: forall n
   . Vector n (Vector StepIPARounds StepField)
  -> StepField
challengesDigest expandedOldBpChals =
  evalPureSpongeM (initialSponge) do
    for_ expandedOldBpChals \inner -> for_ inner absorb
    squeeze

-- | Main port of OCaml `Wrap_deferred_values.expand_deferred`.
-- | All derivation logic reuses `Pickles.Prove.Pure.Common` helpers;
-- | this function's job is to replay the sponge and plumb the carried
-- | minimal values through to the common helpers.
expandDeferredForVerify
  :: forall n
   . ExpandDeferredInput n
  -> WrapDeferredValuesOutput
expandDeferredForVerify input =
  let
    -- ===== Step 1. Endo-expand zeta (needed for zetaw + scalars_env in
    -- derivePlonk). alpha is expanded once below for oraclesReconstructed;
    -- beta/gamma stay in their raw 128-bit form.
    zetaField = coerce (toFieldPure input.rawPlonk.zeta (F input.endo))

    zetaw = zetaField * input.generator

    -- Collapsed evals (= OCaml `Plonk_checks.evals_of_split_evals`)
    -- derived from the chunked form via Horner at `zeta^(2^srsLengthLog2)`.
    -- Used by derivePlonk / ftEval0; the CIP step below consumes the
    -- chunked form directly. NOTE: the sponge absorb just below uses
    -- the collapsed form, which is correct only for inner proofs at
    -- num_chunks=1 (every NEA has length 1 → collapsed equals the only
    -- chunk). For inner proofs with num_chunks > 1 the kimchi prover's
    -- FS sponge absorbs each chunk separately and this replay would
    -- diverge — a separate fix (out of scope for the immediate
    -- chunks2 prover witness convergence, which depends on the wrap
    -- PROVER's CIP only).
    collapsedAllEvals = Chunks.collapseChunkedAllEvals
      { rounds: input.srsLengthLog2
      , zeta: zetaField
      , zetaOmega: zetaw
      }
      input.chunkedAllEvals

    -- ===== Step 2. Sponge replay to recover xi, r. ====================
    -- OCaml: create sponge, absorb sponge_digest_before_evaluations;
    -- then absorb challenges_digest, ft_eval1, and evals (in
    -- `to_absorption_sequence` order); squeeze xi_chal, r_chal as 128-bit.
    -- `input.oldBulletproofChallenges` is already `Ipa.Step.compute_challenges`-
    -- expanded by the caller (step field elements, not raw 128-bit chals).
    { xiRawSized, rRawSized } =
      evalPureSpongeM (initialSponge) do
        absorb input.spongeDigestBeforeEvaluations
        absorb (challengesDigest input.oldBulletproofChallenges)
        absorb input.chunkedAllEvals.ftEval1
        -- Absorb chunked evaluations in the order kimchi's FrSponge does:
        -- `absorb_multiple(&public_evals[0])` then `absorb_multiple(&public_evals[1])`
        -- then `absorb_evaluations(&evals)` which per polynomial absorbs
        -- `absorb(&p.zeta)` (all chunks) then `absorb(&p.zeta_omega)` (all
        -- chunks). For nc=1 this matches the old collapsed single-value path;
        -- for nc>1 it absorbs each chunk, keeping the sponge state in sync
        -- with the prover's FrSponge (which also absorbed each chunk).
        absorbChunked input.chunkedAllEvals.publicEvals
        -- to_absorption_sequence order: z, 6 index, 15 w, 15 coeff, 6 sigma
        absorbChunked input.chunkedAllEvals.zEvals
        for_ input.chunkedAllEvals.indexEvals absorbChunked
        for_ input.chunkedAllEvals.witnessEvals absorbChunked
        for_ input.chunkedAllEvals.coeffEvals absorbChunked
        for_ input.chunkedAllEvals.sigmaEvals absorbChunked
        xiChal <- squeezeScalarChallengePureF
        rChal <- squeezeScalarChallengePureF
        pure { xiRawSized: xiChal, rRawSized: rChal }
      where
      -- Absorb all-zeta chunks then all-zetaw chunks for one polynomial,
      -- matching Rust `absorb(&p.zeta); absorb(&p.zeta_omega)` where each
      -- is a Vec of length num_chunks.
      absorbChunked :: NonEmptyArray _ -> _
      absorbChunked chunks = do
        for_ (NEA.toArray chunks) \pe -> absorb pe.zeta
        for_ (NEA.toArray chunks) \pe -> absorb pe.omegaTimesZeta

    -- Endo-expand xi and r to full field values.
    xiField = coerce (toFieldPure xiRawSized (F input.endo))

    rField = coerce (toFieldPure rRawSized (F input.endo))

    -- ===== Step 3. Type1.derive_plonk (wrap.ml:202-208). ==============
    derivePlonkInput =
      { plonkMinimal: input.rawPlonk
      , w: map _.zeta (Vector.take @7 collapsedAllEvals.witnessEvals)
      , sigma: map _.zeta collapsedAllEvals.sigmaEvals
      , zZeta: collapsedAllEvals.zEvals.zeta
      , zOmegaTimesZeta: collapsedAllEvals.zEvals.omegaTimesZeta
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      }

    stepPlonkDerived = derivePlonk derivePlonkInput

    -- ===== Step 4. ft_eval0 for the step field. =======================
    ftEval0Input =
      { plonkMinimal: input.rawPlonk
      , allEvals: collapsedAllEvals
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

    -- ===== Step 5. combined_inner_product (wrap.ml:22-62, 235-245). ====
    -- Uses chunked evals for CIP to match OCaml's
    -- `Pcs_batch.combine_split_evaluations` xi-batching across chunks.
    cipInput =
      { allEvals: input.chunkedAllEvals
      , publicEvals: input.chunkedAllEvals.publicEvals
      , ftEval0: stepFtEval0
      , ftEval1: input.chunkedAllEvals.ftEval1
      , oldBulletproofChallenges: input.oldBulletproofChallenges
      , xi: xiField
      , r: rField
      , zeta: zetaField
      , zetaw
      }

    cipActual = combinedInnerProductBatchChunked cipInput

    -- ===== Step 6. new bulletproof challenges + b (wrap.ml:209-224). ===
    -- `computeBpChalsAndB` is field-polymorphic; unwrap `F` from raw
    -- chals so `f = StepField` agrees with `endo/zeta/zetaw/r`.
    newBpResult = computeBpChalsAndB
      { rawPrechallenges: map unwrapF input.rawBulletproofChallenges
      , endo: input.endo
      , zeta: zetaField
      , zetaw
      , r: rField
      }

    -- ===== Step 7. oracles — fill in the full OraclesResult. ==========
    -- The verifier can reconstruct every field; downstream code
    -- (assembleWrapMainInput) only reads a subset, but
    -- WrapDeferredValuesOutput expects the full record.
    expandedPlonk =
      { alpha: coerce (toFieldPure input.rawPlonk.alpha (F input.endo)) :: StepField
      , beta: coerce (SizedF.toField input.rawPlonk.beta) :: StepField
      , gamma: coerce (SizedF.toField input.rawPlonk.gamma) :: StepField
      , zeta: zetaField
      }

    -- `OraclesResult f` is field-polymorphic; the existing callers use
    -- `f = StepField` (un-F-wrapped). Unwrap F from the raw sized chals.
    oraclesReconstructed =
      { alpha: expandedPlonk.alpha
      , beta: unwrapF input.rawPlonk.beta
      , gamma: unwrapF input.rawPlonk.gamma
      , zeta: zetaField
      , ftEval0: stepFtEval0
      , v: xiField
      , u: rField
      , combinedInnerProduct: cipActual
      , ftEval1: input.chunkedAllEvals.ftEval1
      , publicEvals: input.chunkedAllEvals.publicEvals
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
        { zeta: collapsedAllEvals.publicEvals.zeta
        , omegaTimesZeta: collapsedAllEvals.publicEvals.omegaTimesZeta
        }
    , spongeDigestBeforeEvaluations: input.spongeDigestBeforeEvaluations
    , oracles: oraclesReconstructed
    , newBulletproofChallenges: newBpResult
    }

-- | Pure squeeze of a 128-bit scalar challenge, wrapped into `F StepField`.
-- | `Pickles.Sponge.squeezeScalarChallengePure` returns `SizedF 128 f`;
-- | our `ScalarChallenge (F StepField)` type wants `SizedF 128 (F StepField)`.
squeezeScalarChallengePureF :: PureSpongeM StepField (SizedF 128 (F StepField))
squeezeScalarChallengePureF = wrapF <$> squeezeScalarChallengePure
