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
-- | Top-level out-of-circuit Pickles verifier — the public surface
-- | for FULLY verifying a Pickles proof.
-- |
-- | Native: `Verifier`, `mkVerifier`, `verify`, `verifyOne`,
-- | `CompiledProof`, `wrapPublicInput(Of)`.
-- |
-- | Re-exports `Pickles.Verify.Types` (`BulletproofChallenges`,
-- | `DeferredValues`, `WrapDeferredValues`, `BranchData`,
-- | `PlonkMinimal`, `PlonkInCircuit`, `ScalarChallenge`,
-- | `UnfinalizedProof`) since these appear in `Verifier`-shaped
-- | values consumers will see.
-- |
-- | `verifyOne` runs three stages per proof; they are internal —
-- | callers see only the bundled `verify` ("proof → yes/no"):
-- |   1. Expand deferred values from the wrap proof's minimal
-- |      skeleton.
-- |   2. Accumulator IPA-step check (Vesta-SRS MSM).
-- |   3. Kimchi `batch_verify` on the wrap proof.
module Pickles.Verify
  ( module Pickles.Verify.Types
  , CompiledProof(..)
  , CompiledProofWidthData(..)
  , SomeCompiledProofWidthData
  , mkSomeCompiledProofWidthData
  , Verifier
  , mkVerifier
  , verifyOne
  , verify
  , wrapPublicInput
  , wrapPublicInputOf
  ) where

import Prelude

import Data.Array as Array
import Data.Exists (Exists, mkExists, runExists)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Constants (zkRows)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (Proof, permutationVanishingPolynomial, verifyOpeningProof)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesInput, WrapDeferredValuesOutput, assembleWrapMainInput)
import Pickles.Types (PaddedLength, StepIPARounds, WrapIPARounds)
import Pickles.Verify.Types (BranchData, BulletproofChallenges, DeferredValues, PlonkExpanded, PlonkInCircuit, PlonkMinimal, ScalarChallenge, UnfinalizedProof, WrapDeferredValues, expandPlonkMinimal, toPlonkMinimal)
import Pickles.Wrap.Types as Wrap
import Prim.Int (class Add)
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
import Type.Proxy (Proxy(..))

-- | Per-tag verification state. Shippable independently of provers —
-- | closes over the wrap VK (small) + Vesta SRS (shared public params)
-- | + the step-domain constants derived from the compiled step circuit.
type Verifier =
  { wrapVK :: VerifierIndex PallasG WrapField
  -- | Step SRS, for the stage-2 accumulator MSM (`compute_sg`).
  , vestaSrs :: CRS VestaG
  -- | Step domain log2 (= `stepProverIndex.domain.log_size_of_group`).
  -- | Per-compiled-circuit — varies depending on constraint count;
  -- | read via `pallasProverIndexDomainLog2` at `mkVerifier` time.
  , stepDomainLog2 :: Int
  -- | Kimchi `zkRows` (`Pickles.Constants.zkRows`).
  , stepZkRows :: Int
  -- | Step SRS size log2. Protocol constant for the Pasta/Pickles cycle
  -- | (= `Common.Max_degree.step_log2` = `StepIPARounds` = 16), NOT a
  -- | per-circuit value — every step proof's IPA rounds are bounded by
  -- | the SRS size, which is fixed by the cycle's design.
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
  , stepZkRows: zkRows
  , stepSrsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
  , stepGenerator: domainGenerator stepDomainLog2 :: StepField
  , stepShifts: domainShifts stepDomainLog2 :: Vector 7 StepField
  , stepEndo: case (endoScalar :: EndoScalar StepField) of EndoScalar e -> e
  , linearizationPoly: Linearization.pallas
  }

-- | The five fields whose Vector size depends on the rule's *actual*
-- | prev step proof count (= OCaml's `'most_recent_width` in
-- | `proof.mli:97-110`). They share the same width because they all
-- | describe per-prev-step-proof data.
-- |
-- | Wrapped behind `Exists` in `CompiledProof` so the per-rule width
-- | is hidden at the outer type — mirrors OCaml's GADT existential
-- | `T : ... -> ('s, 'mlmb) with_data` which exposes only `'mlmb`.
data CompiledProofWidthData :: Int -> Type
data CompiledProofWidthData width = CompiledProofWidthData
  { -- Reified `reflectType (Proxy @width)` for runtime inspection
    -- after `runExists`. PS's `Exists` doesn't preserve type-class
    -- instances across the existential boundary, so the value is
    -- stored explicitly.
    width :: Int

  -- Inner step proof's prev-proof bp challenges (carried by the
  -- wrap proof's `messages_for_next_step_proof` field). Sized at
  -- the rule's actual prev count.
  , oldBulletproofChallenges :: Vector width (Vector StepIPARounds StepField)

  -- Per-prev wrap-side bp-challenges that this proof hashed into
  -- `messagesForNextWrapProofDigest`.
  , msgWrapChallenges :: Vector width (Vector WrapIPARounds WrapField)

  -- Per-prev outer-step `expandProof.sg` values used as real-slot
  -- `sgX/sgY` in `kimchiPrevChallenges` when this proof's wrap
  -- proof was generated.
  , outerStepChalPolyComms :: Vector width (AffinePoint StepField)

  -- | Prover-side `WrapDeferredValuesInput`; carries `prevSgs` and
  -- | `prevChallenges` at the per-rule width. Read only by
  -- | `Test.Pickles.Verify.ExpandDeferredEq`'s self-consistency
  -- | check; `verifyOne` doesn't read it.
  , wrapDvInput :: WrapDeferredValuesInput width

  -- ===== Pre-padded views (front-padded with the matching dummy). =====
  --
  -- Inside `runExists`, `width` is rigid existential, so consumers
  -- can't form an `Add pad width PaddedLength` constraint to pad
  -- with `Vector.append (Vector.replicate @pad dummy) raw`. The
  -- producer (`mkSomeCompiledProofWidthData`) HAS that constraint
  -- (its `width = mpv` is concrete), so it pre-computes the padded
  -- versions and stores them. Downstream callers — `mkStepAdvice` /
  -- `shapeProveData` for `InductivePrev` — read these directly,
  -- which makes their advice assembly Vector-only (no Array
  -- roundtrip). Mirrors OCaml's `Vector.extend_front` of
  -- `messages_for_next_step_proof.old_bulletproof_challenges` etc.
  , oldBulletproofChallengesPadded :: Vector PaddedLength (Vector StepIPARounds StepField)
  , msgWrapChallengesPadded :: Vector PaddedLength (Vector WrapIPARounds WrapField)
  , outerStepChalPolyCommsPadded :: Vector PaddedLength (AffinePoint StepField)
  }

-- | Existentially-quantified `CompiledProofWidthData`. PS analog of
-- | OCaml `Proof.with_data`'s GADT — `width` is hidden; consumers
-- | `runExists` to recover it (in continuation-passing form).
type SomeCompiledProofWidthData = Exists CompiledProofWidthData

-- | Smart constructor for `SomeCompiledProofWidthData`. Pre-computes
-- | the `Vector PaddedLength` views from the unpadded `Vector width`
-- | inputs using the producer's `Add pad width PaddedLength`
-- | constraint, then erases the per-rule `width` axis behind the
-- | existential.
mkSomeCompiledProofWidthData
  :: forall @width @pad
   . Reflectable width Int
  => Reflectable pad Int
  => Add pad width PaddedLength
  => { oldBulletproofChallenges :: Vector width (Vector StepIPARounds StepField)
     , msgWrapChallenges :: Vector width (Vector WrapIPARounds WrapField)
     , outerStepChalPolyComms :: Vector width (AffinePoint StepField)
     , wrapDvInput :: WrapDeferredValuesInput width
     -- Front-padding dummies, one per padded view. Used to fill the
     -- `pad` slots prepended to each `Vector width X` to lift it to
     -- `Vector PaddedLength X`.
     , dummyOldBp :: Vector StepIPARounds StepField
     , dummyMsgWrap :: Vector WrapIPARounds WrapField
     , dummyChalPolyComm :: AffinePoint StepField
     }
  -> SomeCompiledProofWidthData
mkSomeCompiledProofWidthData rec = mkExists $ CompiledProofWidthData
  { width: reflectType (Proxy @width)
  , oldBulletproofChallenges: rec.oldBulletproofChallenges
  , msgWrapChallenges: rec.msgWrapChallenges
  , outerStepChalPolyComms: rec.outerStepChalPolyComms
  , wrapDvInput: rec.wrapDvInput
  , oldBulletproofChallengesPadded:
      Vector.append (Vector.replicate @pad rec.dummyOldBp)
        rec.oldBulletproofChallenges
  , msgWrapChallengesPadded:
      Vector.append (Vector.replicate @pad rec.dummyMsgWrap)
        rec.msgWrapChallenges
  , outerStepChalPolyCommsPadded:
      Vector.append (Vector.replicate @pad rec.dummyChalPolyComm)
        rec.outerStepChalPolyComms
  }

-- | Everything needed to verify one proof, minus the per-tag constants
-- | in `Verifier`. Mirrors the content of OCaml `'mlmb Proof.t` (= the
-- | carried-statement bundle + the actual kimchi opening proof).
-- |
-- | `mpv` is the proof system's *outer* `Max_proofs_verified.n` — the
-- | OCaml `'mlmb` parameter. It pins `Tag _ _ mpv` (= proof system
-- | identity); per-rule width-dependent fields are hidden inside
-- | `widthData :: SomeCompiledProofWidthData` to mirror OCaml's
-- | `'most_recent_width` GADT existential (`proof.mli:97-110`).
newtype CompiledProof :: Int -> Type -> Type -> Type -> Type
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

  -- Inner step proof's evals (carried by the wrap proof's `prev_evals`
  -- field).
  , prevEvals :: AllEvals StepField
  , pEval0Chunks :: Array StepField

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

  -- Per-rule width-dependent fields, hidden via existential. Bundles:
  --   * oldBulletproofChallenges
  --   * msgWrapChallenges
  --   * outerStepChalPolyComms
  --   * wrapDvInput
  -- Mirrors OCaml's `'most_recent_width`-sized vectors hidden by the
  -- `Proof.with_data` GADT existential.
  , widthData :: SomeCompiledProofWidthData

  -- This proof's actual STEP domain log2 (= the proof's branch's
  -- step circuit domain log2). For multi-branch compiled outputs the
  -- shared `Verifier`'s `stepDomainLog2` is a placeholder (the first
  -- branch's), but verifying / re-expanding deferred values for a
  -- specific proof requires its branch's domain log2. Mirrors
  -- OCaml `branch_data.domain_log2` carried in
  -- `proof_state.deferred_values.branch_data`.
  , stepDomainLog2 :: Int

  -- The prover's `Wrap_deferred_values.t`. Surfaced for
  -- self-consistency tests that compare the prover-side computation
  -- (`wrapComputeDeferredValues`) against the verifier-side
  -- reconstruction (`expandDeferredForVerify`) on a real proof. Not
  -- width-dependent (output type doesn't carry mpv).
  , wrapDv :: WrapDeferredValuesOutput
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
    zetaField = coerce (toFieldPure p.rawPlonk.zeta (F verifier.stepEndo))

    -- Per-proof step domain (= the proof's branch's step circuit
    -- domain log2). For multi-branch compiled outputs the shared
    -- verifier's `stepDomainLog2` is a placeholder; the proof's own
    -- `stepDomainLog2` is authoritative.
    pStepGenerator = domainGenerator p.stepDomainLog2

    pStepShifts = domainShifts p.stepDomainLog2

    vanishesOnZkAtZeta = permutationVanishingPolynomial
      { domainLog2: p.stepDomainLog2
      , zkRows: verifier.stepZkRows
      , pt: zetaField
      }

    -- ===== Stage 1: expand deferred values. =====
    -- `oldBulletproofChallenges` is sized at the per-rule width
    -- (hidden by `widthData`'s existential). `runExists` recovers
    -- the typed Vector inside the polymorphic continuation; the
    -- result type is `WrapDeferredValuesOutput` (no width
    -- parameter), so the existential boundary is satisfied.
    dv = runExists
      ( \(CompiledProofWidthData wd) ->
          expandDeferredForVerify
            { rawPlonk: p.rawPlonk
            , rawBulletproofChallenges: p.rawBulletproofChallenges
            , branchData: p.branchData
            , spongeDigestBeforeEvaluations: p.spongeDigestBeforeEvaluations
            , allEvals: p.prevEvals
            , pEval0Chunks: p.pEval0Chunks
            , oldBulletproofChallenges: wd.oldBulletproofChallenges
            , domainLog2: p.stepDomainLog2
            , zkRows: verifier.stepZkRows
            , srsLengthLog2: verifier.stepSrsLengthLog2
            , generator: pStepGenerator
            , shifts: pStepShifts
            , vanishesOnZk: vanishesOnZkAtZeta
            , omegaForLagrange: \_ -> one
            , endo: verifier.stepEndo
            , linearizationPoly: verifier.linearizationPoly
            }
      )
      p.widthData

    -- ===== Stage 2: IPA step accumulator check. =====
    -- OCaml `Ipa.Step.accumulator_check`: verify
    -- `compute_sg(expanded bp-chals) == challengePolynomialCommitment`.
    expandedBpChals = Array.fromFoldable $
      map (\c -> coerce (toFieldPure c (F verifier.stepEndo)) :: StepField)
        p.rawBulletproofChallenges

    computedSg = vestaSrsBPolyCommitmentPoint verifier.vestaSrs expandedBpChals

    accumulatorOk = computedSg == p.challengePolynomialCommitment

    -- ===== Stage 3: kimchi batch_verify on the wrap proof. =====
    pi = wrapPublicInputOf dv p.messagesForNextStepProofDigest p.messagesForNextWrapProofDigest

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
    zetaField = coerce (toFieldPure p.rawPlonk.zeta (F verifier.stepEndo))

    pStepGenerator = domainGenerator p.stepDomainLog2

    pStepShifts = domainShifts p.stepDomainLog2

    vanishesOnZkAtZeta = permutationVanishingPolynomial
      { domainLog2: p.stepDomainLog2
      , zkRows: verifier.stepZkRows
      , pt: zetaField
      }

    -- Same existential-unwrap pattern as `verifyOne`: the per-rule
    -- width is hidden in `widthData`; `runExists` recovers the typed
    -- Vector inside a polymorphic continuation that returns
    -- `WrapDeferredValuesOutput` (no width parameter).
    dv = runExists
      ( \(CompiledProofWidthData wd) ->
          expandDeferredForVerify
            { rawPlonk: p.rawPlonk
            , rawBulletproofChallenges: p.rawBulletproofChallenges
            , branchData: p.branchData
            , spongeDigestBeforeEvaluations: p.spongeDigestBeforeEvaluations
            , allEvals: p.prevEvals
            , pEval0Chunks: p.pEval0Chunks
            , oldBulletproofChallenges: wd.oldBulletproofChallenges
            , domainLog2: p.stepDomainLog2
            , zkRows: verifier.stepZkRows
            , srsLengthLog2: verifier.stepSrsLengthLog2
            , generator: pStepGenerator
            , shifts: pStepShifts
            , vanishesOnZk: vanishesOnZkAtZeta
            , omegaForLagrange: \_ -> one
            , endo: verifier.stepEndo
            , linearizationPoly: verifier.linearizationPoly
            }
      )
      p.widthData
  in
    wrapPublicInputOf dv p.messagesForNextStepProofDigest p.messagesForNextWrapProofDigest

-- | Flatten an expanded `WrapDeferredValuesOutput` + both message digests
-- | into the kimchi public-input array via `assembleWrapMainInput` + the
-- | `Wrap.StatementPacked` `CircuitType` instance.
wrapPublicInputOf
  :: WrapDeferredValuesOutput
  -> StepField
  -> WrapField
  -> Array WrapField
wrapPublicInputOf dv stepDigest wrapDigest =
  let
    packed
      :: Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean
    packed = assembleWrapMainInput
      { deferredValues: dv
      , messagesForNextStepProofDigest: stepDigest
      , messagesForNextWrapProofDigest: wrapDigest
      }
  in
    valueToFields
      @WrapField
      @(Wrap.StatementPacked StepIPARounds (Type1 (F WrapField)) (F WrapField) Boolean)
      packed
