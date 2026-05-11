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

import Data.Foldable (for_)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (OraclesResult)
import Pickles.Prove.Pure.Common (BulletproofBOutput, CombinedInnerProductBatchInput, DerivePlonkInput, FtEval0Input, combinedInnerProductBatch, computeBpChalsAndB, derivePlonk, ftEval0)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesOutput)
import Pickles.Sponge (PureSpongeM, absorb, evalPureSpongeM, initialSponge, squeeze, squeezeScalarChallengePure)
import Pickles.Step.Types (Field)
import Pickles.Types (StepIPARounds)
import Pickles.Verify.Types (BranchData, PlonkInCircuit, PlonkMinimal, ScalarChallenge)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.SizedF (SizedF, unwrapF, wrapF)
import Snarky.Circuit.DSL.SizedF as SizedF
import Snarky.Circuit.Kimchi (Type1, toShifted)
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
-- |   `omegaForLagrange`, `endo` (= `endoScalar @Field`),
-- |   `linearizationPoly`.
type ExpandDeferredInput n =
  { -- Carried (raw) values from the wrap proof's minimal proof state.
    rawPlonk :: PlonkMinimal (F Field)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F Field))
  , branchData :: BranchData Field Boolean
  , spongeDigestBeforeEvaluations :: Field

  -- Evals + prev-proof bp chals (= the inner step proof's data, carried
  -- by the wrap proof).
  , allEvals :: AllEvals Field
  , pEval0Chunks :: Array Field
  , oldBulletproofChallenges :: Vector n (Vector StepIPARounds Field)

  -- Static step-domain / SRS metadata (same source as prover — read from
  -- the step verifier index).
  , domainLog2 :: Int
  , zkRows :: Int
  , srsLengthLog2 :: Int
  , generator :: Field
  , shifts :: Vector 7 Field
  , vanishesOnZk :: Field
  , omegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> Field
  , endo :: Field
  , linearizationPoly :: LinearizationPoly Field
  }

-- | Compute `challenges_digest = sponge(expanded old_bp_chals flattened)`.
-- | Matches the sub-sponge in `wrap_deferred_values.ml:128-137` — a fresh
-- | `Tick_field_sponge.Field` that absorbs every expanded bp-challenge
-- | (outer × inner), then squeezes one field element.
challengesDigest
  :: forall n
   . Vector n (Vector StepIPARounds Field)
  -> Field
challengesDigest expandedOldBpChals =
  evalPureSpongeM (initialSponge :: Sponge Field) do
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
    zetaField :: Field
    zetaField = coerce (toFieldPure input.rawPlonk.zeta (F input.endo))

    zetaw :: Field
    zetaw = zetaField * input.generator

    -- ===== Step 2. Sponge replay to recover xi, r. ====================
    -- OCaml: create sponge, absorb sponge_digest_before_evaluations;
    -- then absorb challenges_digest, ft_eval1, and evals (in
    -- `to_absorption_sequence` order); squeeze xi_chal, r_chal as 128-bit.
    -- `input.oldBulletproofChallenges` is already `Ipa.Step.compute_challenges`-
    -- expanded by the caller (step field elements, not raw 128-bit chals).
    { xiRawSized, rRawSized } =
      evalPureSpongeM (initialSponge :: Sponge Field) do
        absorb input.spongeDigestBeforeEvaluations
        absorb (challengesDigest input.oldBulletproofChallenges)
        absorb input.allEvals.ftEval1
        -- public_input absorb: (zeta, zeta*omega) as single-element "arrays"
        absorb input.allEvals.publicEvals.zeta
        absorb input.allEvals.publicEvals.omegaTimesZeta
        -- to_absorption_sequence order: z, 6 index, 15 w, 15 coeff, 6 sigma
        absorbPointEval input.allEvals.zEvals
        for_ input.allEvals.indexEvals absorbPointEval
        for_ input.allEvals.witnessEvals absorbPointEval
        for_ input.allEvals.coeffEvals absorbPointEval
        for_ input.allEvals.sigmaEvals absorbPointEval
        xiChal <- squeezeScalarChallengePureF
        rChal <- squeezeScalarChallengePureF
        pure { xiRawSized: xiChal, rRawSized: rChal }
      where
      absorbPointEval pe = do
        absorb pe.zeta
        absorb pe.omegaTimesZeta

    -- Endo-expand xi and r to full field values.
    xiField :: Field
    xiField = coerce (toFieldPure xiRawSized (F input.endo))

    rField :: Field
    rField = coerce (toFieldPure rRawSized (F input.endo))

    -- ===== Step 3. Type1.derive_plonk (wrap.ml:202-208). ==============
    derivePlonkInput :: DerivePlonkInput Field
    derivePlonkInput =
      { plonkMinimal: input.rawPlonk
      , w: map _.zeta (Vector.take @7 input.allEvals.witnessEvals)
      , sigma: map _.zeta input.allEvals.sigmaEvals
      , zZeta: input.allEvals.zEvals.zeta
      , zOmegaTimesZeta: input.allEvals.zEvals.omegaTimesZeta
      , shifts: input.shifts
      , generator: input.generator
      , domainLog2: input.domainLog2
      , zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , endo: input.endo
      }

    stepPlonkDerived :: PlonkInCircuit (F Field) (Type1 (F Field))
    stepPlonkDerived = derivePlonk derivePlonkInput

    -- ===== Step 4. ft_eval0 for the step field. =======================
    ftEval0Input :: FtEval0Input Field
    ftEval0Input =
      { plonkMinimal: input.rawPlonk
      , allEvals: input.allEvals
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

    stepFtEval0 :: Field
    stepFtEval0 = ftEval0 ftEval0Input

    -- ===== Step 5. combined_inner_product (wrap.ml:22-62, 235-245). ====
    cipInput :: CombinedInnerProductBatchInput n StepIPARounds Field
    cipInput =
      { allEvals: input.allEvals
      , publicEvals: input.allEvals.publicEvals
      , ftEval0: stepFtEval0
      , ftEval1: input.allEvals.ftEval1
      , oldBulletproofChallenges: input.oldBulletproofChallenges
      , xi: xiField
      , r: rField
      , zeta: zetaField
      , zetaw
      }

    cipActual :: Field
    cipActual = combinedInnerProductBatch cipInput

    -- ===== Step 6. new bulletproof challenges + b (wrap.ml:209-224). ===
    -- `computeBpChalsAndB` is field-polymorphic; unwrap `F` from raw
    -- chals so `f = Field` agrees with `endo/zeta/zetaw/r`.
    newBpResult :: BulletproofBOutput StepIPARounds Field
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
      { alpha: coerce (toFieldPure input.rawPlonk.alpha (F input.endo)) :: Field
      , beta: coerce (SizedF.toField input.rawPlonk.beta) :: Field
      , gamma: coerce (SizedF.toField input.rawPlonk.gamma) :: Field
      , zeta: zetaField
      }

    -- `OraclesResult f` is field-polymorphic; the existing callers use
    -- `f = Field` (un-F-wrapped). Unwrap F from the raw sized chals.
    oraclesReconstructed :: OraclesResult Field
    oraclesReconstructed =
      { alpha: expandedPlonk.alpha
      , beta: unwrapF input.rawPlonk.beta
      , gamma: unwrapF input.rawPlonk.gamma
      , zeta: zetaField
      , ftEval0: stepFtEval0
      , v: xiField
      , u: rField
      , combinedInnerProduct: cipActual
      , ftEval1: input.allEvals.ftEval1
      , publicEvalZeta: input.allEvals.publicEvals.zeta
      , publicEvalZetaOmega: input.allEvals.publicEvals.omegaTimesZeta
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
        { zeta: input.allEvals.publicEvals.zeta
        , omegaTimesZeta: input.allEvals.publicEvals.omegaTimesZeta
        }
    , spongeDigestBeforeEvaluations: input.spongeDigestBeforeEvaluations
    , oracles: oraclesReconstructed
    , newBulletproofChallenges: newBpResult
    }

-- | Pure squeeze of a 128-bit scalar challenge, wrapped into `F Field`.
-- | `Pickles.Sponge.squeezeScalarChallengePure` returns `SizedF 128 f`;
-- | our `ScalarChallenge (F Field)` type wants `SizedF 128 (F Field)`.
squeezeScalarChallengePureF :: PureSpongeM Field (SizedF 128 (F Field))
squeezeScalarChallengePureF = wrapF <$> squeezeScalarChallengePure
