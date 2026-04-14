-- | Step-prover orchestration: pure PS ports of the two top-level
-- | step-prover helpers in OCaml pickles.
-- |
-- | This module consolidates what used to live in two files:
-- |
-- | * `Pickles.Prove.Pure.ExpandDeferred` — the step-field Type1
-- |   deferred-value derivation for one wrap-proof predecessor
-- |   (OCaml `wrap_deferred_values.ml:15-199`). Internal helper.
-- | * `Pickles.Prove.Pure.ExpandProof` — the full
-- |   per-predecessor `expand_proof` (OCaml `step.ml:122-537`) that
-- |   the step prover runs for each wrap proof it wraps. Top-level
-- |   entry point.
-- |
-- | Both live in the step prover's code path; they share the
-- | `ExpandDeferredOutput` shape (`expandProof` consumes it).
-- |
-- | All scalar math (`derivePlonk`, `ftEval0`, `combinedInnerProductBatch`,
-- | `computeBpChalsAndB`, `actualEvaluation`) lives in
-- | `Pickles.Prove.Pure.Common` and is field-polymorphic; this module
-- | just plumbs step-field vs wrap-field instantiations and the
-- | sponge pipeline / FFI calls.
module Pickles.Prove.Pure.Step
  ( -- * Step-field Type1 deferred-value derivation
    ExpandDeferredInput
  , ExpandDeferredOutput
  , expandDeferred
  -- * Full per-predecessor expand_proof
  , ExpandProofInput
  , ExpandProofOutput
  , PrevStatementWithHashes
  , expandProof
  ) where

import Prelude

import Data.Fin (unsafeFinite)
import Data.Foldable (for_)
import Data.Maybe (fromJust)
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector, (!!))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.IPA (bPoly)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals, absorbAllEvals)
import Pickles.ProofFFI (OraclesResult, Proof, domainGenerator, proofOpeningPrechallenges, vestaChallengePolyCommitment, vestaProofCommitments, vestaProofOpeningDelta, vestaProofOpeningLr, vestaProofOpeningSg, vestaProofOpeningZ1, vestaProofOpeningZ2, vestaProofOracles)
import Pickles.Prove.Pure.Common (BulletproofBOutput, CombinedInnerProductBatchInput, DerivePlonkInput, FtEval0Input, combinedInnerProductBatch, computeBpChalsAndB, derivePlonk, ftEval0)
import Pickles.Sponge (absorb, evalPureSpongeM, initialSponge, squeeze, squeezeScalarChallengePure)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Types (FopProofState(..), StepAllEvals, StepField, StepIPARounds, StepPerProofWitness(..), StepProofState(..), WrapField, WrapIPARounds, WrapProof(..), WrapProofMessages(..), WrapProofOpening(..))
import Pickles.Types as PT
import Pickles.VerificationKey (StepVK)
import Pickles.Verify.Types (BranchData, PlonkInCircuit, PlonkMinimal, ScalarChallenge, UnfinalizedProof)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Circuit.DSL (F(..), UnChecked(..))
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField, unwrapF, wrapF)
import Snarky.Circuit.Kimchi (SplitField, Type1, Type2, toFieldPure, toShifted)
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint, WeierstrassAffinePoint(..))

--------------------------------------------------------------------------------
-- expandDeferred
--
-- Pure PS port of OCaml's `Wrap_deferred_values.expand_deferred`
-- (`mina/src/lib/crypto/pickles/wrap_deferred_values.ml:15-199`).
--
-- Despite the OCaml module path, this is the **step-field** deferred
-- value derivation: given a wrap proof's raw deferred values + its
-- polynomial evaluations, it produces the Type1 shifted
-- `Deferred_values.t` that step_main consumes.
--
-- OCaml body (high level):
--
-- 1. Endo-expand plonk minimal challenges (alpha, zeta).
-- 2. `evals_of_split_evals` → recombine chunked evals (we assume
--    the caller has done this already).
-- 3. Build a step-field `scalars_env` (via `Common.ftEval0`'s internal
--    `fieldEnv` call).
-- 4. `derive_plonk` (Type1 instantiation) → scalar derivations for
--    the plonk record, with raw alpha/beta/gamma/zeta preserved.
-- 5. Two-sponge pipeline:
--    - Sub-sponge absorbs expanded previous-proof bp challenges,
--      squeezes one `challenges_digest` field.
--    - Main sponge is seeded with `sponge_digest_before_evaluations`,
--      absorbs `challenges_digest`, `ft_eval1`, then the chunked
--      public_input arrays and the `to_absorption_sequence` of all
--      polynomial evaluation pairs. (For non-chunked, PS's
--      `absorbAllEvals` matches the OCaml order exactly.)
--    - Squeeze two raw 128-bit scalar challenges: `xi_chal` and
--      `r_chal`.
-- 6. Call `combinedInnerProductBatch` (OCaml
--    `Wrap.combined_inner_product`) with expanded xi/r and expanded
--    previous-proof bp challenges.
-- 7. Expand this proof's own bulletproof challenges.
-- 8. `b_actual = b_poly(zeta) + r * b_poly(zetaw)` with b_poly over
--    this proof's own expanded bp challenges.
-- 9. Wrap `combined_inner_product_actual` and `b_actual` in
--    `Shifted_value.Type1` via `toShifted`.
--
-- Non-chunked assumption: every polynomial evaluation is a single
-- value per (zeta, zeta·omega) pair. For standard Mina circuits,
-- `num_chunks = 1`, so this matches production.
--------------------------------------------------------------------------------

-- | Input to `expandDeferred`.
-- |
-- | Type parameters:
-- |
-- | * `n` — number of previous proofs whose bp challenges contribute
-- |   a b_poly to the batched CIP.
-- | * `d` — length of each bulletproof challenge vector (= step IPA
-- |   rounds).
type ExpandDeferredInput n d =
  { zkRows :: Int
  , srsLengthLog2 :: Int

  -- Polynomial evals (recombined — caller applied
  -- `Common.evalsOfSplitPoint` upstream).
  , allEvals :: AllEvals StepField
  -- public_input evaluation at zeta, as a chunks array. For non-chunked
  -- circuits (num_chunks = 1), this is a singleton
  -- `[allEvals.publicEvals.zeta]`. Required as-is because `ftEval0`
  -- folds it via zeta_to_srs_length.
  , pEval0Chunks :: Array StepField

  -- Previous-proof bulletproof challenges (raw 128-bit), one vector
  -- per previous proof.
  , oldBulletproofChallenges :: Vector n (Vector d (SizedF 128 (F StepField)))

  -- Raw deferred-values data from the wrap proof's proof state.
  , plonkMinimal :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector d (SizedF 128 (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField

  -- Step domain info (caller derives this from branch_data).
  , generator :: StepField
  , domainLog2 :: Int
  , shifts :: Vector 7 StepField
  , vanishesOnZk :: StepField
  , omegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> StepField

  -- Endo scalar for challenge expansion (= Endo.Wrap_inner_curve.scalar
  -- in OCaml, i.e. `endoScalar @Vesta.BaseField @Vesta.ScalarField`).
  , endo :: StepField

  -- Linearization token stream for the wrap circuit whose proof is
  -- being expanded (Tick linearization = `Pickles.Linearization.pallas`).
  , linearizationPoly :: LinearizationPoly StepField
  }

-- | Output of `expandDeferred`: the Type1-shifted deferred values
-- | that step_main reads.
-- |
-- | Matches OCaml's `Types.Wrap.Proof_state.Deferred_values.t` shape:
-- |
-- | * `plonk` — raw 128-bit challenges preserved on alpha/beta/gamma/zeta,
-- |   Type1 shifted values on perm/zetaToDomainSize/zetaToSrsLength.
-- | * `combinedInnerProduct` — Type1 shift of the batched eval sum.
-- | * `xi` — raw 128-bit challenge freshly squeezed from the main
-- |   sponge (NOT the `xi` field of the input proof state: that value
-- |   is cross-checked elsewhere by the verifier).
-- | * `bulletproofChallenges` — this proof's own bp challenges,
-- |   endo-expanded to full step-field elements.
-- | * `b` — Type1 shift of `b_poly(zeta) + r * b_poly(zetaw)` where
-- |   b_poly uses the same expanded bp challenges.
-- | * `branchData` — passed through from the input proof state.
type ExpandDeferredOutput d =
  { plonk :: PlonkInCircuit (F StepField) (Type1 (F StepField))
  , combinedInnerProduct :: Type1 (F StepField)
  , xi :: ScalarChallenge (F StepField)
  , bulletproofChallenges :: Vector d StepField
  , b :: Type1 (F StepField)
  , branchData :: BranchData StepField Boolean
  }

-- | Compute the Type1-shifted deferred values that step_main consumes
-- | for one predecessor wrap proof.
expandDeferred
  :: forall n d
   . Reflectable d Int
  => ExpandDeferredInput n d
  -> ExpandDeferredOutput d
expandDeferred input =
  let
    -- Endo-expand a raw 128-bit SizedF challenge to a full step-field
    -- element. `unwrapF` strips the `F` newtype so `toFieldPure`'s
    -- signature (`SizedF 128 f -> f -> f`) matches.
    expandChal :: SizedF 128 (F StepField) -> StepField
    expandChal c = toFieldPure (unwrapF c) input.endo

    -- Step 1: derive_plonk (Type1 instantiation — return type pins
    -- the Shifted instance).
    derivePlonkInput :: DerivePlonkInput StepField
    derivePlonkInput =
      { plonkMinimal: input.plonkMinimal
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

    derivedPlonk :: PlonkInCircuit (F StepField) (Type1 (F StepField))
    derivedPlonk = derivePlonk derivePlonkInput

    -- Step 2: ft_eval0 (Type1 instantiation — step field + pallas
    -- linearization).
    ftEval0Input :: FtEval0Input StepField
    ftEval0Input =
      { plonkMinimal: input.plonkMinimal
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

    stepFtEval0 :: StepField
    stepFtEval0 = ftEval0 ftEval0Input

    -- Step 3: expand previous-proof bp challenges (used both for the
    -- challenges_digest sub-sponge and for combined_inner_product's
    -- b_poly inputs).
    prevExpanded :: Vector n (Vector d StepField)
    prevExpanded = map (map expandChal) input.oldBulletproofChallenges

    -- Step 4a: sub-sponge over flattened expanded prev challenges.
    challengesDigest :: StepField
    challengesDigest = evalPureSpongeM initialSponge do
      for_ prevExpanded \chals -> for_ chals (absorb :: StepField -> _)
      squeeze

    -- Step 4b: main sponge squeezes (xi_chal, r_chal) after absorbing
    -- sponge_digest, challenges_digest, and all polynomial evaluations.
    -- `absorbAllEvals` matches OCaml's `ft_eval1, public, z, index,
    -- witness, coeff, sigma` order in the non-chunked case.
    mainSqueezes
      :: { xiRaw :: SizedF 128 StepField, rRaw :: SizedF 128 StepField }
    mainSqueezes = evalPureSpongeM initialSponge do
      absorb input.spongeDigestBeforeEvaluations
      absorb challengesDigest
      absorbAllEvals input.allEvals
      xiRaw <- squeezeScalarChallengePure
      rRaw <- squeezeScalarChallengePure
      pure { xiRaw, rRaw }

    -- Endo-expand xi and r for use in combined_inner_product.
    xiExpanded = toFieldPure mainSqueezes.xiRaw input.endo
    rExpanded = toFieldPure mainSqueezes.rRaw input.endo

    -- zetaw = zeta * omega (needed for b_poly and CIP's zetaw side).
    zetaField = toFieldPure (unwrapF input.plonkMinimal.zeta) input.endo
    zetaw = zetaField * input.generator

    -- Step 5: combined_inner_product (field-polymorphic, specialised
    -- here to StepField via the input types).
    cipInputRec :: CombinedInnerProductBatchInput n d StepField
    cipInputRec =
      { allEvals: input.allEvals
      , publicEvals: input.allEvals.publicEvals
      , ftEval0: stepFtEval0
      , ftEval1: input.allEvals.ftEval1
      , oldBulletproofChallenges: prevExpanded
      , xi: xiExpanded
      , r: rExpanded
      , zeta: zetaField
      , zetaw
      }

    cipActual :: StepField
    cipActual = combinedInnerProductBatch cipInputRec

    -- Step 6: this proof's own expanded bp challenges + b_actual via
    -- b_poly at zeta and zetaw.
    ownExpanded :: Vector d StepField
    ownExpanded = map expandChal input.rawBulletproofChallenges

    bActual :: StepField
    bActual =
      bPoly ownExpanded zetaField
        + rExpanded * bPoly ownExpanded zetaw

    -- The main sponge returns `SizedF 128 StepField` (unwrapped); the
    -- output type expects `SizedF 128 (F StepField)` to match
    -- `ScalarChallenge (F StepField)`. Both are newtypes over `StepField`
    -- so `wrapF` is a zero-cost coercion.
    xiOutput :: ScalarChallenge (F StepField)
    xiOutput = wrapF mainSqueezes.xiRaw
  in
    { plonk: derivedPlonk
    , combinedInnerProduct: toShifted (F cipActual)
    , xi: xiOutput
    , bulletproofChallenges: ownExpanded
    , b: toShifted (F bActual)
    , branchData: input.branchData
    }

--------------------------------------------------------------------------------
-- expandProof
--
-- Top-level PS port of OCaml `expand_proof` (`step.ml:122-537`). The
-- step prover runs this for each wrap proof it wraps, producing the
-- witness values the step circuit reads via the `Req.*` requests.
--
-- The body plumbs the pure helpers in `Common` (derivePlonk,
-- ftEval0, combinedInnerProductBatch, computeBpChalsAndB), the
-- step-field `expandDeferred` from this module, the
-- message-hash helpers in `Pickles.{Step,Wrap}.MessageHash`, and the
-- wrap-proof FFI in `Pickles.ProofFFI`.
--
-- OCaml body structure (step.ml line → PS wiring):
--
-- * 140-148 graft app_state                 → caller responsibility (input)
-- * 149     Wrap_wire_proof.to_kimchi_proof → FFI conversion (not yet)
-- * 150-225 step-field derive_plonk         → subsumed by `expandDeferred`
-- * 230-235 prev_challenges (expand)        → inline `toFieldPure` fold
-- * 236-241 `expand_deferred` call          → `expandDeferred`
-- * 242-297 prev_statement_with_hashes      → `hashMessagesForNext{Step,Wrap}Proof*`
-- * 298-317 wrap oracles FFI                → `vestaProofOracles`
-- * 319-343 extract oracle outputs          → field projections
-- * 359-379 new bp challenges + b           → `computeBpChalsAndB`
-- * 380-383 challenge_polynomial_commitment → `vestaProofOpeningSg` / `vestaChallengePolyCommitment`
-- * 384-410 Per_proof_witness assembly      → `wrapProofKimchi` + `stepProofState`
-- * 411-511 wrap-field Type2 plonk          → `derivePlonk` (Type2 instance)
-- * 464-496 combined_inner_product wrap-f   → `combinedInnerProductBatch`
-- * 512-536 Shifted Type2, assemble output  → record wiring + `toShifted`
--------------------------------------------------------------------------------

-- | Input to `expandProof` — one raw wrap proof + per-predecessor
-- | metadata.
-- |
-- | Type parameters:
-- |
-- | * `n` — number of previous proofs whose bp challenges feed the
-- |   CIP batching on the **step side** (= `actual_proofs_verified`
-- |   in OCaml for the step proof being built).
-- | * `nwp` — number of padded challenge vectors on the **wrap side**
-- |   (= `Wrap_hack.Padded_length.n = 2`; caller has already padded).
-- |
-- | Inner bp-challenge vector lengths are fixed at the concrete
-- | `StepIPARounds` / `WrapIPARounds` type aliases per field, based
-- | on which IPA the challenges came from (see each field's doc).
type ExpandProofInput n nwp =
  { -- Runtime flag: false for dummy predecessors the step circuit
    -- elides verification of.
    mustVerify :: Boolean

  -- ===== Inputs to `expandDeferred` (step-field Type1 deferred values) =====

  -- Plonk-checks constants for the wrap circuit being expanded.
  , zkRows :: Int
  , srsLengthLog2 :: Int

  -- Polynomial evaluations from the wrap proof, already recombined
  -- via `Common.evalsOfSplitPoint` upstream (non-chunked assumption).
  , allEvals :: AllEvals StepField
  , pEval0Chunks :: Array StepField

  -- Previous-proof bulletproof challenges (raw 128-bit step-field
  -- challenges). Inner length `StepIPARounds` per OCaml `Step_bp_vec.t`.
  , oldBulletproofChallenges :: Vector n (Vector StepIPARounds (SizedF 128 (F StepField)))

  -- Raw deferred-values data from the wrap proof's statement.
  , plonkMinimal :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (SizedF 128 (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField

  -- Step domain info derived from branch_data.
  , stepDomainLog2 :: Int
  , stepGenerator :: StepField
  , stepShifts :: Vector 7 StepField
  , stepVanishesOnZk :: StepField
  , stepOmegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> StepField

  -- Endo scalar for step-field challenge expansion.
  , endo :: StepField

  -- Linearization token stream for the wrap circuit (Tick linearization).
  , linearizationPoly :: LinearizationPoly StepField

  -- ===== `prev_statement_with_hashes` step-side digest =====
  -- These are everything `Common.hash_messages_for_next_step_proof`
  -- reads, via `Reduced_messages_for_next_proof_over_same_field.Step.prepare`
  -- (reduced_messages_for_next_proof_over_same_field.ml:32-43).

  -- The wrap circuit's VK commitments (`dlog_plonk_index` in OCaml).
  , dlogIndex :: StepVK StepField
  -- The predecessor's app-state projected to field elements.
  , appStateFields :: Array StepField
  -- The previous proofs' challenge-polynomial commitments (each a
  -- wrap-proof `sg` = Pallas point with step-field coordinates). One
  -- per entry in `oldBulletproofChallenges`.
  , stepPrevSgs :: Vector n (AffinePoint StepField)

  -- ===== `prev_statement_with_hashes` wrap-side digest =====
  -- Inputs to `Wrap_hack.hash_messages_for_next_wrap_proof` (wrap_hack.ml:46-59).

  -- The wrap proof's own challenge-polynomial commitment. OCaml type
  -- `Tick.Curve.Affine.t` = Vesta affine (Vesta.BaseField = WrapField).
  , wrapChallengePolynomialCommitment :: AffinePoint WrapField
  -- Padded previous bp challenges for the wrap-side hash, already
  -- expanded to WrapField and padded to `nwp = Wrap_hack.Padded_length.n = 2`.
  , wrapPaddedPrevChallenges :: Vector nwp (Vector WrapIPARounds WrapField)

  -- ===== Wrap-proof oracles (FFI) =====
  , wrapVerifierIndex :: VerifierIndex PallasG WrapField
  , wrapProof :: Proof PallasG WrapField
  , tockPublicInput :: Array WrapField

  -- ===== New bulletproof challenges + b =====
  , wrapDomainLog2 :: Int
  , wrapEndo :: WrapField

  -- ===== Wrap-field Type2 deferred values (`unfinalized` output) =====
  , wrapAllEvals :: AllEvals WrapField
  , wrapPEval0Chunks :: Array WrapField
  , wrapShifts :: Vector 7 WrapField
  , wrapZkRows :: Int
  , wrapSrsLengthLog2 :: Int
  , wrapVanishesOnZk :: WrapField
  , wrapOmegaForLagrange :: { zkRows :: Boolean, offset :: Int } -> WrapField
  , wrapLinearizationPoly :: LinearizationPoly WrapField

  -- ===== `perProofWitness` (`Per_proof_witness.Constant.t`) =====

  -- The wrap proof's embedded `prev_evals` — evaluations of the step
  -- proof it wraps, in **step field**. OCaml step.ml:390 reads this
  -- as `t.prev_evals`.
  , stepProofPrevEvals :: StepAllEvals (F StepField)

  -- Pre-expanded, pre-padded step-side previous bp challenges.
  -- Caller applies `Ipa.Step.compute_challenges` to the raw ones from
  -- `statement.messages_for_next_step_proof.old_bulletproof_challenges`
  -- and extends with `Dummy.Ipa.Step.challenges_computed` to reach
  -- `Local_max_proofs_verified.n = 1`.
  , stepPrevChallenges :: Vector 1 (Vector StepIPARounds (F StepField))

  -- Pre-padded step-side previous challenge-polynomial commitments
  -- (sgs). Separate from `stepPrevSgs` (unpadded, used by the hash).
  , stepPrevSgsPadded :: Vector 1 (AffinePoint StepField)
  }

-- | Output of `expandProof` — the witness data the step circuit
-- | reads for one predecessor slot. Maps to OCaml's return tuple
-- | from `expand_proof` (step.ml:515-536).
type ExpandProofOutput =
  { sg :: AffinePoint StepField
  -- | The wrap-field deferred-value record + should_finalize flag +
  -- | sponge digest. Corresponds to OCaml `Unfinalized.Constant.t`.
  -- | Native wrap field + same-field Type2 shifts; cross-field
  -- | limb-packing happens downstream when this is allocated as a
  -- | step-circuit witness.
  , unfinalized ::
      UnfinalizedProof
        WrapIPARounds
        (F WrapField)
        (Type2 (F WrapField))
        Boolean
  -- | Public input polynomial evaluation at (zeta, zeta·omega). In
  -- | OCaml (step.ml:319) these are `Tock.Field.t` values from the
  -- | wrap oracles (= `WrapField`).
  , xHat :: { zeta :: WrapField, omegaTimesZeta :: WrapField }
  , perProofWitness ::
      StepPerProofWitness
        1
        StepIPARounds
        WrapIPARounds
        (F StepField)
        (Type2 (SplitField (F StepField) Boolean))
        Boolean
  , actualWrapDomain :: Int
  -- | The `prev_statement_with_hashes` tuple item from OCaml's
  -- | `expand_proof` return (step.ml:133).
  , prevStatementWithHashes :: PrevStatementWithHashes
  -- | Raw wrap-proof oracle output.
  , oracles :: OraclesResult WrapField
  -- | New bulletproof challenges (endo-expanded) + combined opening
  -- | target `b = b_poly(zeta) + r·b_poly(zetaw)`, in the wrap field.
  , newBulletproofChallenges :: BulletproofBOutput WrapIPARounds WrapField
  }

-- | The digests that `prev_statement_with_hashes` carries at the
-- | hash boundary between the step prover and the wrap oracles.
-- |
-- | * `messagesForNextStepProof` — step-field Poseidon digest of the
-- |   VK + app_state + prev (sg, bp_challenges) pairs. Computed by
-- |   `Common.hash_messages_for_next_step_proof` at OCaml
-- |   `common.ml:45-52`.
-- | * `messagesForNextWrapProof` — wrap-field Poseidon digest of the
-- |   padded prev bp_challenges + own sg. Computed by
-- |   `Wrap_hack.hash_messages_for_next_wrap_proof` at
-- |   `wrap_hack.ml:46-59`.
type PrevStatementWithHashes =
  { messagesForNextStepProof :: F StepField
  , messagesForNextWrapProof :: F WrapField
  }

-- | The main `expand_proof` port.
expandProof
  :: forall n nwp
   . ExpandProofInput n nwp
  -> ExpandProofOutput
expandProof input =
  let
    -- ===== Step-field Type1 deferred values. =====
    --
    -- Collapses OCaml step.ml:150-225 (local `derive_plonk`) and
    -- step.ml:236-241 (`Wrap_deferred_values.expand_deferred`) into
    -- a single call, because `expandDeferred` internally does the
    -- same `derive_plonk` OCaml redundantly recomputes locally.
    _deferredStep :: ExpandDeferredOutput StepIPARounds
    _deferredStep = expandDeferred
      { zkRows: input.zkRows
      , srsLengthLog2: input.srsLengthLog2
      , allEvals: input.allEvals
      , pEval0Chunks: input.pEval0Chunks
      , oldBulletproofChallenges: input.oldBulletproofChallenges
      , plonkMinimal: input.plonkMinimal
      , rawBulletproofChallenges: input.rawBulletproofChallenges
      , branchData: input.branchData
      , spongeDigestBeforeEvaluations: input.spongeDigestBeforeEvaluations
      , generator: input.stepGenerator
      , domainLog2: input.stepDomainLog2
      , shifts: input.stepShifts
      , vanishesOnZk: input.stepVanishesOnZk
      , omegaForLagrange: input.stepOmegaForLagrange
      , endo: input.endo
      , linearizationPoly: input.linearizationPoly
      }

    -- ===== Step-side hash of `messages_for_next_step_proof`. =====
    --
    -- Matches OCaml step.ml:256-265 (`Reduced_messages_for_next_proof
    -- _over_same_field.Step.prepare` + `Common.hash_messages_for_next
    -- _step_proof`). `prepare` expands each raw bp challenge via the
    -- step endo; we zip prev sgs with the expanded challenge vectors
    -- into the shape `hashMessagesForNextStepProofPure` expects.
    stepPrevProofs =
      Vector.zipWith
        ( \sg raw ->
            { sg
            , expandedBpChallenges:
                map (\c -> toFieldPure (unwrapF c) input.endo) raw
            }
        )
        input.stepPrevSgs
        input.oldBulletproofChallenges

    messagesForNextStepProofDigest :: StepField
    messagesForNextStepProofDigest = hashMessagesForNextStepProofPure
      { stepVk: input.dlogIndex
      , appState: input.appStateFields
      , proofs: stepPrevProofs
      }

    -- ===== Wrap-side hash of `messages_for_next_wrap_proof`. =====
    --
    -- Matches OCaml step.ml:288-294 (`Wrap_hack.hash_messages_for_next
    -- _wrap_proof`). Caller pre-expanded and pre-padded the prev bp
    -- challenges (`pad_challenges` lives outside our scope).
    messagesForNextWrapProofDigest :: WrapField
    messagesForNextWrapProofDigest = hashMessagesForNextWrapProofPureGeneral
      { sg: input.wrapChallengePolynomialCommitment
      , paddedChallenges: input.wrapPaddedPrevChallenges
      }

    -- ===== Wrap-proof oracles (Tock/Pallas FFI). =====
    --
    -- Runs kimchi's Fiat-Shamir oracle computation on the wrap proof.
    -- Matches OCaml step.ml:298-343.
    --
    -- TODO(recursive-prev-challenges): OCaml's `O.create` takes a
    -- `Challenge_polynomial.t list` (step.ml:304-317) built from
    -- `stepPrevSgsPadded` and expanded wrap-field prev bp challenges.
    -- For a base-case / non-recursive VK (where
    -- `verifier_index.prev_challenges = 0`) an empty list is correct
    -- and produces the same transcript kimchi computed at
    -- proof-creation time. Once we exercise an inductive test, thread
    -- the real list through here by populating `prevChallenges`.
    oraclesResult :: OraclesResult WrapField
    oraclesResult = vestaProofOracles input.wrapVerifierIndex
      { proof: input.wrapProof
      , publicInput: input.tockPublicInput
      , prevChallenges: []
      }

    -- ===== New bulletproof challenges + b (step.ml:359-379). =====
    --
    -- The FFI returns an Array of raw 128-bit field elements; we
    -- reflect its length at `WrapIPARounds` via `toVector` and wrap
    -- each element as a `SizedF 128`. Kimchi's `ScalarChallenge`
    -- contract guarantees the 128-bit bound, so `unsafeFromField` is
    -- safe here.
    rawPrechalsArray :: Array WrapField
    rawPrechalsArray = proofOpeningPrechallenges input.wrapVerifierIndex
      { proof: input.wrapProof
      , publicInput: input.tockPublicInput
      }

    rawPrechalsVec :: Vector WrapIPARounds (SizedF 128 WrapField)
    rawPrechalsVec = unsafePartial $ fromJust $
      Vector.toVector @WrapIPARounds
        (map (unsafePartial unsafeFromField) rawPrechalsArray)

    wrapGen :: WrapField
    wrapGen = domainGenerator input.wrapDomainLog2

    wrapZetaw :: WrapField
    wrapZetaw = oraclesResult.zeta * wrapGen

    newBpResult :: BulletproofBOutput WrapIPARounds WrapField
    newBpResult = computeBpChalsAndB
      { rawPrechallenges: rawPrechalsVec
      , endo: input.wrapEndo
      , zeta: oraclesResult.zeta
      , zetaw: wrapZetaw
      , r: oraclesResult.u
      }

    -- ===== challenge_polynomial_commitment (step.ml:380-383). =====
    --
    --     if not must_verify
    --       then Ipa.Wrap.compute_sg new_bulletproof_challenges
    --       else proof.openings.proof.challenge_polynomial_commitment
    challengePolynomialCommitment :: AffinePoint StepField
    challengePolynomialCommitment =
      if input.mustVerify then
        vestaProofOpeningSg input.wrapProof
      else
        vestaChallengePolyCommitment input.wrapVerifierIndex
          (Vector.toUnfoldable newBpResult.chals)

    -- ===== Wrap-field Type2 deferred values (`Unfinalized.Constant.t`). =====
    --
    -- Matches OCaml step.ml:411-536. The wrap-field `plonk`,
    -- `ft_eval0`, and `combined_inner_product` are computed using the
    -- same field-polymorphic helpers from `Common` — only the field
    -- and the caller-supplied linearization poly change.

    -- Build the wrap-field `PlonkMinimal` from raw oracle outputs.
    -- OCaml step.ml:323-334 assembles this from `O.alpha`, `O.beta`,
    -- `O.gamma`, `O.zeta` — all raw 128-bit. Our FFI surfaces them as
    -- bare `SizedF 128 WrapField`; we wrap with `wrapF` to match
    -- `PlonkMinimal (F WrapField)`.
    wrapPlonkMinimal :: PlonkMinimal (F WrapField)
    wrapPlonkMinimal =
      { alpha: wrapF oraclesResult.alphaChal
      , beta: wrapF oraclesResult.beta
      , gamma: wrapF oraclesResult.gamma
      , zeta: wrapF oraclesResult.zetaChal
      }

    -- derive_plonk for the wrap field (Type2 instantiation via the
    -- same `Common.derivePlonk` body; the `Shifted` instance is
    -- picked by the return-type annotation).
    wrapDerivePlonkInput :: DerivePlonkInput WrapField
    wrapDerivePlonkInput =
      { plonkMinimal: wrapPlonkMinimal
      , w: map _.zeta (Vector.take @7 input.wrapAllEvals.witnessEvals)
      , sigma: map _.zeta input.wrapAllEvals.sigmaEvals
      , zZeta: input.wrapAllEvals.zEvals.zeta
      , zOmegaTimesZeta: input.wrapAllEvals.zEvals.omegaTimesZeta
      , shifts: input.wrapShifts
      , generator: wrapGen
      , domainLog2: input.wrapDomainLog2
      , zkRows: input.wrapZkRows
      , srsLengthLog2: input.wrapSrsLengthLog2
      , endo: input.wrapEndo
      }

    wrapPlonkDerived :: PlonkInCircuit (F WrapField) (Type2 (F WrapField))
    wrapPlonkDerived = derivePlonk wrapDerivePlonkInput

    -- ft_eval0 for the wrap field — matches step.ml:487-492.
    wrapFtEval0Input :: FtEval0Input WrapField
    wrapFtEval0Input =
      { plonkMinimal: wrapPlonkMinimal
      , allEvals: input.wrapAllEvals
      , pEval0Chunks: input.wrapPEval0Chunks
      , shifts: input.wrapShifts
      , generator: wrapGen
      , domainLog2: input.wrapDomainLog2
      , zkRows: input.wrapZkRows
      , srsLengthLog2: input.wrapSrsLengthLog2
      , endo: input.wrapEndo
      , vanishesOnZk: input.wrapVanishesOnZk
      , omegaForLagrange: input.wrapOmegaForLagrange
      , linearizationPoly: input.wrapLinearizationPoly
      }

    wrapFtEval0 :: WrapField
    wrapFtEval0 = ftEval0 wrapFtEval0Input

    -- Wrap-field combined_inner_product (step.ml:464-496).
    -- `oracles.v` = polyscale (xi), `oracles.u` = evalscale (r). Both
    -- are already endo-expanded by the FFI.
    wrapCipInput :: CombinedInnerProductBatchInput nwp WrapIPARounds WrapField
    wrapCipInput =
      { allEvals: input.wrapAllEvals
      , publicEvals:
          { zeta: oraclesResult.publicEvalZeta
          , omegaTimesZeta: oraclesResult.publicEvalZetaOmega
          }
      , ftEval0: wrapFtEval0
      , ftEval1: oraclesResult.ftEval1
      , oldBulletproofChallenges: input.wrapPaddedPrevChallenges
      , xi: oraclesResult.v
      , r: oraclesResult.u
      , zeta: oraclesResult.zeta
      , zetaw: wrapZetaw
      }

    wrapCip :: WrapField
    wrapCip = combinedInnerProductBatch wrapCipInput

    -- Assemble the `DeferredValues` + `Unfinalized` records.
    wrapUnfinalized
      :: UnfinalizedProof WrapIPARounds (F WrapField) (Type2 (F WrapField)) Boolean
    wrapUnfinalized =
      { deferredValues:
          { plonk: wrapPlonkDerived
          , combinedInnerProduct: toShifted (F wrapCip)
          , xi: wrapF oraclesResult.vChal
          , bulletproofChallenges: map wrapF rawPrechalsVec
          , b: toShifted (F newBpResult.b)
          }
      , shouldFinalize: input.mustVerify
      , spongeDigestBeforeEvaluations: F oraclesResult.fqDigest
      }

    -- ===== `perProofWitness` (`Per_proof_witness.Constant.t`). =====
    --
    -- Matches OCaml step.ml:384-410. Builds the structured witness
    -- the step circuit reads via `Req.Proof_with_datas`. The kimchi
    -- in-memory wrap proof is unpacked into the PS `WrapProof`
    -- record via FFI getters; the rest comes from previously
    -- computed values or caller-supplied inputs.

    -- Convert a bare Pallas affine point (coords in StepField) to
    -- `WeierstrassAffinePoint PallasG (F StepField)`.
    mkPallasPt
      :: AffinePoint StepField
      -> WeierstrassAffinePoint PallasG (F StepField)
    mkPallasPt pt = WeierstrassAffinePoint { x: F pt.x, y: F pt.y }

    wrapCommits = vestaProofCommitments input.wrapProof

    wrapProofMessages
      :: WrapProofMessages (WeierstrassAffinePoint PallasG (F StepField))
    wrapProofMessages = WrapProofMessages
      { wComm: map mkPallasPt wrapCommits.wComm
      , zComm: mkPallasPt wrapCommits.zComm
      , tComm:
          unsafePartial fromJust $
            Vector.toVector @7 (map mkPallasPt wrapCommits.tComm)
      }

    -- Wrap proof's opening proof from the kimchi form. The `sg`
    -- commitment is replaced with `challengePolynomialCommitment`
    -- (our computed one) to match OCaml step.ml:404-408's
    -- `{ proof.openings.proof with challenge_polynomial_commitment }`.
    lrArray :: Array { l :: WeierstrassAffinePoint PallasG (F StepField), r :: WeierstrassAffinePoint PallasG (F StepField) }
    lrArray = vestaProofOpeningLr input.wrapProof <#> \pair ->
      { l: mkPallasPt pair.l, r: mkPallasPt pair.r }

    wrapProofOpening
      :: WrapProofOpening
           WrapIPARounds
           (WeierstrassAffinePoint PallasG (F StepField))
           (Type2 (SplitField (F StepField) Boolean))
    wrapProofOpening = WrapProofOpening
      { lr: unsafePartial fromJust $ Vector.toVector @WrapIPARounds lrArray
      , z1: toShifted (F (vestaProofOpeningZ1 input.wrapProof))
      , z2: toShifted (F (vestaProofOpeningZ2 input.wrapProof))
      , delta: mkPallasPt (vestaProofOpeningDelta input.wrapProof)
      , sg: mkPallasPt challengePolynomialCommitment
      }

    wrapProofKimchi
      :: WrapProof
           WrapIPARounds
           (WeierstrassAffinePoint PallasG (F StepField))
           (Type2 (SplitField (F StepField) Boolean))
    wrapProofKimchi = WrapProof
      { messages: wrapProofMessages
      , opening: wrapProofOpening
      }

    -- `StepProofState` = the wrap proof's step-field Type1 deferred
    -- values, flattened into `FopProofState`, plus `BranchData`.
    -- Matches OCaml step.ml:266-285.
    stepPlonkDerived :: PlonkInCircuit (F StepField) (Type1 (F StepField))
    stepPlonkDerived = _deferredStep.plonk

    -- Convert the `Verify.Types.BranchData` record (flat with
    -- `proofsVerifiedMask :: Vector 2 _`) into the
    -- `Pickles.Types.BranchData` newtype (mask0/mask1 named fields,
    -- `F`-wrapped domainLog2). Same data, different packaging.
    stepBranchData :: PT.BranchData (F StepField) Boolean
    stepBranchData =
      let
        v = _deferredStep.branchData.proofsVerifiedMask
      in
        PT.BranchData
          { mask0: v !! unsafeFinite @2 0
          , mask1: v !! unsafeFinite @2 1
          , domainLog2: F _deferredStep.branchData.domainLog2
          }

    stepProofState :: StepProofState StepIPARounds (F StepField) Boolean
    stepProofState = StepProofState
      -- The 5 fp slots store the **shifted inner** form (matching
      -- OCaml's `Per_proof_witness.proof_state.deferred_values.plonk`
      -- at the var level). See the longer note at the parallel site in
      -- `Pickles.Prove.Step.getStepPerProofWitnesses` for why we do
      -- NOT call `fromShifted` here.
      { fopState: FopProofState
          { combinedInnerProduct: unwrap _deferredStep.combinedInnerProduct
          , b: unwrap _deferredStep.b
          , zetaToSrsLength: unwrap stepPlonkDerived.zetaToSrsLength
          , zetaToDomainSize: unwrap stepPlonkDerived.zetaToDomainSize
          , perm: unwrap stepPlonkDerived.perm
          , spongeDigest: F input.spongeDigestBeforeEvaluations
          , beta: UnChecked stepPlonkDerived.beta
          , gamma: UnChecked stepPlonkDerived.gamma
          , alpha: UnChecked stepPlonkDerived.alpha
          , zeta: UnChecked stepPlonkDerived.zeta
          , xi: UnChecked _deferredStep.xi
          , bulletproofChallenges: map UnChecked input.rawBulletproofChallenges
          }
      , branchData: stepBranchData
      }

    perProofWitnessAssembled
      :: StepPerProofWitness
           1
           StepIPARounds
           WrapIPARounds
           (F StepField)
           (Type2 (SplitField (F StepField) Boolean))
           Boolean
    perProofWitnessAssembled = StepPerProofWitness
      { wrapProof: wrapProofKimchi
      , proofState: stepProofState
      , prevEvals: input.stepProofPrevEvals
      , prevChallenges: map UnChecked input.stepPrevChallenges
      , prevSgs: map mkPallasPt input.stepPrevSgsPadded
      }
  in
    { sg: challengePolynomialCommitment
    , unfinalized: wrapUnfinalized
    , xHat:
        { zeta: oraclesResult.publicEvalZeta
        , omegaTimesZeta: oraclesResult.publicEvalZetaOmega
        }
    , perProofWitness: perProofWitnessAssembled
    -- step.ml:536 reads this from `dlog_vk.domain.log_size_of_group`.
    , actualWrapDomain: input.wrapDomainLog2
    , prevStatementWithHashes:
        { messagesForNextStepProof: F messagesForNextStepProofDigest
        , messagesForNextWrapProof: F messagesForNextWrapProofDigest
        }
    , oracles: oraclesResult
    , newBulletproofChallenges: newBpResult
    }
