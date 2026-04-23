-- | Top-level out-of-circuit Pickles verifier.
-- |
-- | This is the PS counterpart to OCaml `Pickles.verify_promise` /
-- | `Verify.verify_heterogenous` (`mina/src/lib/crypto/pickles/verify.ml`).
-- | A `Verifier` is what you ship to a client; a `CompiledProof` is what
-- | a prover hands over; `verify` tells you whether the proof is valid
-- | for its claimed statement.
-- |
-- | Internally, `verifyOne` runs the three stages OCaml's
-- | `verify_heterogenous` runs for each proof:
-- |
-- | 1. **Expand deferred values** (stage 1) — reconstruct the full
-- |    `WrapDeferredValuesOutput` from the wrap proof's carried minimal
-- |    skeleton via `Pickles.Prove.Pure.Verify.expandDeferredForVerify`.
-- |    Matches OCaml `Wrap_deferred_values.expand_deferred`.
-- |
-- | 2. **Accumulator (IPA step) check** (stage 2) — verify
-- |    `Ipa.Step.compute_sg(expanded bp-chals) == challengePolynomialCommitment`
-- |    via a Vesta-SRS MSM. This is the expensive IPA check Pickles
-- |    defers through the recursion.
-- |
-- | 3. **Kimchi batch-verify on the wrap proof** (stage 3) — assemble
-- |    the wrap public input from the expanded deferred values + the
-- |    two message digests via `assembleWrapMainInput`, flatten via
-- |    `CircuitType`, hand it to `pallasVerifyOpeningProof`.
-- |
-- | The separation between `Verifier` (per-tag constants — wrap VK,
-- | Vesta SRS, step domain metadata) and `CompiledProof` (per-proof
-- | data) mirrors how OCaml `compile_promise` returns a
-- | `(module Proof_intf)` that wraps the verifier-needed constants plus
-- | proofs of type `'max_proofs_verified Proof.t`.
module Pickles
  ( CompiledProof(..)
  , Verifier
  , mkVerifier
  , verifyOne
  , verify
  , wrapPublicInput
  ) where

import Prelude

import Data.Array as Array
import Data.Vector (Vector)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (Proof, permutationVanishingPolynomial, verifyOpeningProof)
import Pickles.Prove.Pure.Verify (ExpandDeferredInput, expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesOutput, assembleWrapMainInput)
import Pickles.Types (StepField, StepIPARounds, WrapField, WrapStatementPacked)
import Pickles.Verify.Types (BranchData, PlonkMinimal, ScalarChallenge)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaSrsBPolyCommitmentPoint)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Circuit.Types (valueToFields)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Per-tag verification state. Shippable independently of provers —
-- | closes over the wrap VK (small) + Vesta SRS (shared public params)
-- | + the step-domain constants derived from the compiled step circuit.
type Verifier =
  { wrapVK :: VerifierIndex PallasG WrapField
  -- | Step SRS, for the stage-2 accumulator MSM (`compute_sg`).
  , vestaSrs :: CRS VestaG
  -- | Step domain log2 (= `stepProverIndex.domain.log_size_of_group`).
  , stepDomainLog2 :: Int
  -- | Kimchi `zkRows` (= 3 in standard Mina).
  , stepZkRows :: Int
  -- | Step SRS size log2 (= `Max_degree.step_log2`, = 16 in Mina).
  , stepSrsLengthLog2 :: Int
  -- | Step domain generator `omega` (= `domain_generator stepDomainLog2`).
  , stepGenerator :: StepField
  -- | Permutation shifts for the step domain.
  , stepShifts :: Vector 7 StepField
  -- | Step-field scalar endo coefficient (= `endoScalar @StepField`).
  , stepEndo :: StepField
  -- | Tick linearization polynomial (= `Pickles.Linearization.pallas`).
  , linearizationPoly :: LinearizationPoly StepField
  }

-- | Build a `Verifier` from the minimum the caller supplies (a compiled
-- | wrap VK, a Vesta SRS, and the step domain log2). All derived
-- | constants (generator, shifts, endo, linearization) come from the
-- | standard Pickles setup.
mkVerifier
  :: { wrapVK :: VerifierIndex PallasG WrapField
     , vestaSrs :: CRS VestaG
     , stepDomainLog2 :: Int
     }
  -> Verifier
mkVerifier { wrapVK, vestaSrs, stepDomainLog2 } =
  { wrapVK
  , vestaSrs
  , stepDomainLog2
  , stepZkRows: 3
  , stepSrsLengthLog2: 16
  , stepGenerator: domainGenerator stepDomainLog2 :: StepField
  , stepShifts: domainShifts stepDomainLog2 :: Vector 7 StepField
  , stepEndo: case (endoScalar :: EndoScalar StepField) of EndoScalar e -> e
  , linearizationPoly: Linearization.pallas
  }

-- | Everything needed to verify one proof, minus the per-tag constants
-- | in `Verifier`. Mirrors the content of OCaml `'n Proof.t` (= the
-- | carried-statement bundle + the actual kimchi opening proof).
newtype CompiledProof mpv stmtVal outputVal auxVal = CompiledProof
  { -- Application-level data.
    statement :: stmtVal
  , publicOutput :: outputVal
  , auxiliaryOutput :: auxVal

  -- The actual wrap kimchi proof (commitments on Pallas, eval field = Fq).
  , wrapProof :: Proof PallasG WrapField

  -- Wrap proof's minimal statement skeleton (input to stage 1 /
  -- `expandDeferredForVerify`). Raw 128-bit scalar challenges — the
  -- endo expansion happens inside the verifier.
  , rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField

  -- Inner step proof's evals + prev-proof bp challenges (carried by the
  -- wrap proof's `prev_evals` / `messages_for_next_step_proof` fields).
  , prevEvals :: AllEvals StepField
  , pEval0Chunks :: Array StepField
  , oldBulletproofChallenges :: Vector mpv (Vector StepIPARounds StepField)

  -- For stage 2 (accumulator check): the inner step proof's IPA opening
  -- sg, which must equal `compute_sg(rawBulletproofChallenges)` on the
  -- step SRS. Lives in `messages_for_next_wrap_proof.challenge_polynomial_commitment`.
  , challengePolynomialCommitment :: AffinePoint WrapField

  -- Pre-hashed message digests (both ends of the recursion). OCaml's
  -- verify.ml hashes these from the raw messages in the verifier; here
  -- we keep them pre-hashed on the prover side (same value). See
  -- `Pickles.Step.MessageHash.hashMessagesForNextStepProofPure` +
  -- `Pickles.Wrap.MessageHash.hashMessagesForNextWrapProofPureGeneral`.
  , messagesForNextStepProofDigest :: StepField
  , messagesForNextWrapProofDigest :: WrapField
  }

-- | Verify one proof. Returns `true` iff all three stages pass.
verifyOne
  :: forall mpv stmtVal outputVal auxVal
   . Verifier
  -> CompiledProof mpv stmtVal outputVal auxVal
  -> Boolean
verifyOne verifier (CompiledProof p) =
  let
    -- Endo-expand zeta once — needed for `vanishesOnZk` and passed into
    -- `expandDeferredForVerify` internally via its own endo expansion.
    zetaField :: StepField
    zetaField = coerce (toFieldPure p.rawPlonk.zeta (F verifier.stepEndo))

    vanishesOnZkAtZeta :: StepField
    vanishesOnZkAtZeta = permutationVanishingPolynomial
      { domainLog2: verifier.stepDomainLog2
      , zkRows: verifier.stepZkRows
      , pt: zetaField
      }

    -- ===== Stage 1: expand deferred values. =====
    dvInput :: ExpandDeferredInput mpv
    dvInput =
      { rawPlonk: p.rawPlonk
      , rawBulletproofChallenges: p.rawBulletproofChallenges
      , branchData: p.branchData
      , spongeDigestBeforeEvaluations: p.spongeDigestBeforeEvaluations
      , allEvals: p.prevEvals
      , pEval0Chunks: p.pEval0Chunks
      , oldBulletproofChallenges: p.oldBulletproofChallenges
      , domainLog2: verifier.stepDomainLog2
      , zkRows: verifier.stepZkRows
      , srsLengthLog2: verifier.stepSrsLengthLog2
      , generator: verifier.stepGenerator
      , shifts: verifier.stepShifts
      , vanishesOnZk: vanishesOnZkAtZeta
      , omegaForLagrange: \_ -> one
      , endo: verifier.stepEndo
      , linearizationPoly: verifier.linearizationPoly
      }
    dv = expandDeferredForVerify dvInput

    -- ===== Stage 2: IPA step accumulator check. =====
    -- OCaml `Ipa.Step.accumulator_check`: verify
    -- `compute_sg(expanded bp-chals) == challengePolynomialCommitment`.
    expandedBpChals :: Array StepField
    expandedBpChals = Array.fromFoldable $
      map (\c -> coerce (toFieldPure c (F verifier.stepEndo)) :: StepField)
        p.rawBulletproofChallenges

    computedSg :: AffinePoint WrapField
    computedSg = vestaSrsBPolyCommitmentPoint verifier.vestaSrs expandedBpChals

    accumulatorOk :: Boolean
    accumulatorOk = computedSg == p.challengePolynomialCommitment

    -- ===== Stage 3: kimchi batch_verify on the wrap proof. =====
    pi :: Array WrapField
    pi = wrapPublicInputOf dv p.messagesForNextStepProofDigest p.messagesForNextWrapProofDigest

    kimchiOk :: Boolean
    kimchiOk = verifyOpeningProof verifier.wrapVK
      { proof: p.wrapProof, publicInput: pi }
  in
    accumulatorOk && kimchiOk

-- | Batch-verify an array of compiled proofs (all of the same tag).
-- |
-- | Currently folds single-proof kimchi verification; kimchi's real
-- | amortized `batch_verify` is exposed via the Rust side but not yet
-- | wired through as a multi-proof FFI function. Functionally correct
-- | regardless.
verify
  :: forall mpv stmtVal outputVal auxVal
   . Verifier
  -> Array (CompiledProof mpv stmtVal outputVal auxVal)
  -> Boolean
verify v = Array.all (verifyOne v)

-- | Assemble the flat `Array WrapField` that `pallasVerifyOpeningProof`
-- | accepts as its `publicInput`. Exposed as a public helper so tests
-- | can cross-check against the prover's assembled `wrapResult.publicInputs`
-- | without running verification end-to-end.
wrapPublicInput
  :: forall mpv stmtVal outputVal auxVal
   . Verifier
  -> CompiledProof mpv stmtVal outputVal auxVal
  -> Array WrapField
wrapPublicInput verifier (CompiledProof p) =
  let
    zetaField :: StepField
    zetaField = coerce (toFieldPure p.rawPlonk.zeta (F verifier.stepEndo))

    vanishesOnZkAtZeta :: StepField
    vanishesOnZkAtZeta = permutationVanishingPolynomial
      { domainLog2: verifier.stepDomainLog2
      , zkRows: verifier.stepZkRows
      , pt: zetaField
      }

    dv = expandDeferredForVerify
      { rawPlonk: p.rawPlonk
      , rawBulletproofChallenges: p.rawBulletproofChallenges
      , branchData: p.branchData
      , spongeDigestBeforeEvaluations: p.spongeDigestBeforeEvaluations
      , allEvals: p.prevEvals
      , pEval0Chunks: p.pEval0Chunks
      , oldBulletproofChallenges: p.oldBulletproofChallenges
      , domainLog2: verifier.stepDomainLog2
      , zkRows: verifier.stepZkRows
      , srsLengthLog2: verifier.stepSrsLengthLog2
      , generator: verifier.stepGenerator
      , shifts: verifier.stepShifts
      , vanishesOnZk: vanishesOnZkAtZeta
      , omegaForLagrange: \_ -> one
      , endo: verifier.stepEndo
      , linearizationPoly: verifier.linearizationPoly
      }
  in
    wrapPublicInputOf dv p.messagesForNextStepProofDigest p.messagesForNextWrapProofDigest

-- | Flatten an expanded `WrapDeferredValuesOutput` + both message digests
-- | into the kimchi public-input array via `assembleWrapMainInput` + the
-- | `WrapStatementPacked` `CircuitType` instance.
wrapPublicInputOf
  :: WrapDeferredValuesOutput
  -> StepField
  -> WrapField
  -> Array WrapField
wrapPublicInputOf dv stepDigest wrapDigest =
  let
    packed
      :: WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
    packed = assembleWrapMainInput
      { deferredValues: dv
      , messagesForNextStepProofDigest: stepDigest
      , messagesForNextWrapProofDigest: wrapDigest
      }
  in
    valueToFields
      @WrapField
      @(WrapStatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean)
      packed
