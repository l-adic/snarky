-- | Top-level out-of-circuit Pickles verifier.
-- |
-- | This is the PS counterpart to OCaml `Pickles.verify_promise` /
-- | `Verify.verify_heterogenous` (`mina/src/lib/crypto/pickles/verify.ml`).
-- | A `Verifier` is what you ship to a client; a `CompiledProof` is what
-- | a prover hands over; `verify` tells you whether the proof is valid
-- | for its claimed statement.
-- |
-- | Internally, `perProof` runs the stages OCaml's
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
-- | 3. **Recompute the two message digests** — the
-- |    `messages_for_next_step_proof` digest from the REAL wrap VK, the
-- |    claimed application state and the carried prev `(sg, challenges)`
-- |    (OCaml `verify.ml`, `Common.hash_messages_for_next_step_proof`
-- |    with `~app_state`), and the `messages_for_next_wrap_proof` digest
-- |    from the carried `sg` and the dummy-padded prev wrap challenges
-- |    (`Wrap_hack.hash_messages_for_next_wrap_proof`). The verifier never
-- |    trusts a prover-supplied digest: these two hashes are what bind
-- |    the whole chain to the verification key and to the statement.
-- |
-- | 4. **Kimchi batch-verify on the wrap proof** (stage 3) — assemble
-- |    the wrap public input from the expanded deferred values + the
-- |    two recomputed digests via `assembleWrapMainInput`, flatten via
-- |    `CircuitType`, rebuild the proof's accumulator list from the
-- |    carried messages (`wrapAccumulators`, OCaml `verify.ml`'s
-- |    `message`), and hand both to the kimchi batch verifier. The list
-- |    the prover stored in the proof object is never used: it would let
-- |    the prover open the wrap proof at accumulators unrelated to the
-- |    `sg` it hashed.
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
-- | `perProof` runs the stages per proof; they are internal —
-- | callers see only the bundled `verify` ("proof → yes/no"):
-- |   1. Expand deferred values from the wrap proof's minimal
-- |      skeleton.
-- |   2. Accumulator IPA-step check (Vesta-SRS MSM).
-- |   3. Recompute both message digests from the wrap VK, the claimed
-- |      application state and the carried prev-proof data.
-- |   4. Kimchi `batch_verify` on the wrap proof.
module Pickles.Verify
  ( module Pickles.Verify.Types
  , CompiledProof(..)
  , CompiledProofWidthData(..)
  , SomeCompiledProofWidthData
  , mkSomeCompiledProofWidthData
  , Verifier
  , VerifiableProof
  , dummyWrapSgOf
  , messageDigests
  , mkVerifier
  , toVerifiable
  , verify
  , verifyBatch
  , verifyStages
  , wrapAccumulators
  , wrapPublicInput
  , wrapPublicInputOf
  ) where

import Prelude

import Data.Array as Array
import Data.Exists (Exists, mkExists, runExists)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Constants (zkRowsForNumChunks)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.PlonkChecks (AllEvals, ChunkedAllEvals)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesOutput, assembleWrapMainInput)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Types (PaddedLength, StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.VerificationKey (extractWrapVKForStepHash)
import Pickles.Verify.Types (BranchData, BulletproofChallenges, DeferredValues, PlonkExpanded, PlonkInCircuit, PlonkMinimal, ScalarChallenge, UnfinalizedProof, WrapDeferredValues, expandPlonkMinimal, toPlonkMinimal)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Pickles.Wrap.Types as Wrap
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Impl.Pallas (pallasSrsBPolyCommitmentPoint)
import Snarky.Backend.Kimchi.Impl.Vesta (vestaSrsBPolyCommitmentPoint)
import Snarky.Backend.Kimchi.Proof (Proof, permutationVanishingPolynomial, verifyOpeningProofsBatch)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.Kimchi (Type1)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Circuit.Types (valueToFields)
import Snarky.Curves.Class (EndoScalar(..), endoScalar)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

-- | Per-tag verification state. Shippable independently of provers —
-- | closes over the wrap VK (small) + Vesta SRS (shared public params)
-- | + the step-domain constants derived from the compiled step circuit.
type Verifier =
  { wrapVK :: VerifierIndex PallasG WrapField
  -- | Step SRS, for the stage-2 accumulator MSM (`compute_sg`).
  , vestaSrs :: CRS VestaG
  -- | Kimchi `zkRows` (`Pickles.Constants.zkRows`).
  , stepZkRows :: Int
  -- | Step SRS size log2. Protocol constant for the Pasta/Pickles cycle
  -- | (= `Common.Max_degree.step_log2` = `StepIPARounds` = 16), NOT a
  -- | per-circuit value — every step proof's IPA rounds are bounded by
  -- | the SRS size, which is fixed by the cycle's design.
  , stepSrsLengthLog2 :: Int
  -- | Step-field scalar endo coefficient (= `endoScalar @StepField`).
  , stepEndo :: StepField
  -- | Tick linearization polynomial (= `Pickles.Linearization.pallas`).
  , linearizationPoly :: LinearizationPoly StepField
  -- | The accumulator a padding slot carries (OCaml `Dummy.Ipa.Wrap.sg`):
  -- | the challenge-polynomial commitment of the dummy wrap challenges on
  -- | the Pallas SRS. `wrapAccumulators` pads with it.
  , dummyWrapSg :: AffinePoint StepField
  }

-- | OCaml `Dummy.Ipa.Wrap.sg`: `compute_sg` of the dummy wrap challenges on
-- | the Pallas SRS, the commitment every dummy-padded accumulator slot
-- | carries.
dummyWrapSgOf :: CRS PallasG -> AffinePoint StepField
dummyWrapSgOf pallasSrs =
  pallasSrsBPolyCommitmentPoint pallasSrs (Vector.toUnfoldable dummyIpaChallenges.wrapExpanded)

-- | Build a `Verifier` from the minimum the caller supplies (a compiled
-- | wrap VK, the two SRSes, and the step `numChunks` driving zk_rows). All
-- | derived constants (endo, linearization, the dummy accumulator) come
-- | from the standard Pickles setup. The per-proof step domain log2
-- | (= generator + shifts) is carried by each `VerifiableProof`'s
-- | `stepDomainLog2` and rebuilt at verify time — see [`verifyOne`].
mkVerifier
  :: { wrapVK :: VerifierIndex PallasG WrapField
     , pallasSrs :: CRS PallasG
     , vestaSrs :: CRS VestaG
     , stepNumChunks :: Int
     }
  -> Verifier
mkVerifier { wrapVK, pallasSrs, vestaSrs, stepNumChunks } =
  { wrapVK
  , vestaSrs
  , stepZkRows: zkRowsForNumChunks stepNumChunks
  , stepSrsLengthLog2: reflectType (Proxy :: Proxy StepIPARounds)
  , stepEndo: case (endoScalar) of EndoScalar e -> e
  , linearizationPoly: Linearization.pallas
  , dummyWrapSg: dummyWrapSgOf pallasSrs
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
-- | OCaml `'mlmb` parameter. It pins `Tag _ mpv` (= proof system
-- | identity); per-rule width-dependent fields are hidden inside
-- | `widthData :: SomeCompiledProofWidthData` to mirror OCaml's
-- | `'most_recent_width` GADT existential (`proof.mli:97-110`).
newtype CompiledProof :: Int -> Type -> Type
newtype CompiledProof mpv stmtVal = CompiledProof
  { -- Application-level data. The statement bundles the rule's
    -- application input + output (the production prover uses
    -- `StatementIO inputVal outputVal`); reach the output via
    -- `(unwrap cp.statement).output` at consumer sites.
    statement :: stmtVal

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
  --
  -- `prevEvalsChunked` is the authoritative form — `NonEmptyArray
  -- (PointEval _)` per polynomial, one entry per chunk. CIP consumes
  -- this directly via `combinedInnerProductBatchChunked`.
  --
  -- `prevEvals` is the COLLAPSED form (chunks Horner-recombined at the
  -- step proof's oracle zeta/zetaw). Kept on the record as a
  -- transitional back-compat shim for the recursive-step
  -- `wrapPrevEvals`/`stepAdvicePrevEvals` plumbing (`Pickles.Prove.Step`)
  -- that still consumes the single-eval form. At step num_chunks=1 it
  -- is byte-identical to the only chunk; at num_chunks>1 it is the
  -- correct Horner combine. The fully-chunked refactor of those
  -- recursive consumers is task #63's follow-up.
  , prevEvals :: AllEvals StepField
  , prevEvalsChunked :: ChunkedAllEvals StepField
  , pEval0Chunks :: Array StepField

  -- For stage 2 (accumulator check): the inner step proof's IPA opening
  -- sg, which must equal `compute_sg(rawBulletproofChallenges)` on the
  -- step SRS. Lives in `messages_for_next_wrap_proof.challenge_polynomial_commitment`.
  , challengePolynomialCommitment :: AffinePoint WrapField

  -- The application state exactly as the step circuit absorbed it into
  -- the `messages_for_next_step_proof` digest: the rule's public input
  -- fields followed by its public output fields (`Pickles.Step.Main`'s
  -- `hashAppFields`). The verifier recomputes that digest from these
  -- fields and the real wrap VK; no digest is carried.
  , appState :: Array StepField

  -- Per-rule width-dependent fields, hidden via existential. Bundles:
  --   * oldBulletproofChallenges
  --   * msgWrapChallenges
  --   * outerStepChalPolyComms
  -- Mirrors OCaml's `'most_recent_width`-sized vectors hidden by the
  -- `Proof.with_data` GADT existential.
  , widthData :: SomeCompiledProofWidthData

  -- This proof's actual STEP domain log2 (= the proof's branch's
  -- step circuit domain log2). Verifying / re-expanding deferred values
  -- requires the proof's own branch's domain log2; the `Verifier` is
  -- shared across branches and rebuilds domain constants (generator,
  -- shifts) from this value at verify time. Mirrors OCaml
  -- `branch_data.domain_log2` carried in
  -- `proof_state.deferred_values.branch_data`.
  , stepDomainLog2 :: Int
  }

-- | The minimal, serializable proof an out-of-circuit verifier actually
-- | consumes: the wrap kimchi proof, the carried statement skeleton, and
-- | the raw messages both message digests are recomputed from. Everything
-- | else a `CompiledProof` carries — the typed application `statement`,
-- | the collapsed `prevEvals` — is irrelevant to verification, so it isn't
-- | here. The per-rule prev-proof width is erased to plain `Array`s; the
-- | three prev-indexed arrays are aligned slot by slot.
-- |
-- | The two message digests are deliberately NOT fields: a digest the
-- | prover supplied would let the prover choose which wrap VK and which
-- | application state the chain is bound to. `messageDigests` recomputes
-- | them, as OCaml's `verify.ml` does.
type VerifiableProof =
  { wrapProof :: Proof PallasG WrapField
  , rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField
  , prevEvalsChunked :: ChunkedAllEvals StepField
  , pEval0Chunks :: Array StepField
  -- The claimed application state, as `CompiledProof.appState`.
  , appState :: Array StepField
  -- `messages_for_next_step_proof`: per prev proof, its expanded
  -- 16-round step challenges and its challenge-polynomial commitment.
  , oldBulletproofChallenges :: Array (Vector StepIPARounds StepField)
  , prevChallengePolynomialCommitments :: Array (AffinePoint StepField)
  -- `messages_for_next_wrap_proof`: this proof's inner step opening `sg`
  -- (also the accumulator-check target) and, per prev proof, its
  -- expanded 15-round wrap challenges.
  , challengePolynomialCommitment :: AffinePoint WrapField
  , prevWrapBulletproofChallenges :: Array (Vector WrapIPARounds WrapField)
  , stepDomainLog2 :: Int
  }

-- | Project a prover-produced `CompiledProof` to the `VerifiableProof` the
-- | verifier needs, erasing the per-rule width existential.
toVerifiable
  :: forall mpv stmtVal
   . CompiledProof mpv stmtVal
  -> VerifiableProof
toVerifiable (CompiledProof p) =
  runExists
    ( \(CompiledProofWidthData wd) ->
        { wrapProof: p.wrapProof
        , rawPlonk: p.rawPlonk
        , rawBulletproofChallenges: p.rawBulletproofChallenges
        , branchData: p.branchData
        , spongeDigestBeforeEvaluations: p.spongeDigestBeforeEvaluations
        , prevEvalsChunked: p.prevEvalsChunked
        , pEval0Chunks: p.pEval0Chunks
        , appState: p.appState
        , oldBulletproofChallenges: Array.fromFoldable wd.oldBulletproofChallenges
        , prevChallengePolynomialCommitments: Array.fromFoldable wd.outerStepChalPolyComms
        , challengePolynomialCommitment: p.challengePolynomialCommitment
        , prevWrapBulletproofChallenges: Array.fromFoldable wd.msgWrapChallenges
        , stepDomainLog2: p.stepDomainLog2
        }
    )
    p.widthData

-- | The two message digests of the wrap statement, recomputed from the
-- | verifier's wrap VK and the proof's carried raw messages. This is the
-- | binding step of OCaml's `verify.ml`: the step digest absorbs the REAL
-- | wrap VK commitments (`Common.hash_messages_for_next_step_proof
-- | ~dlog_plonk_index:key.commitments`), the claimed `app_state`, and each
-- | prev proof's `(sg, expanded step challenges)`; the wrap digest absorbs
-- | the prev wrap challenges front-padded with dummies to `PaddedLength`
-- | (`Wrap_hack.pad_challenges`) and this proof's inner `sg`. Both land in
-- | the wrap public input, so a proof whose step circuit hashed any other
-- | key or state fails the kimchi check.
messageDigests
  :: Verifier
  -> VerifiableProof
  -> { step :: StepField, wrap :: WrapField }
messageDigests verifier vp =
  let
    stepProofs = Array.zipWith
      (\sg expandedBpChallenges -> { sg, expandedBpChallenges })
      vp.prevChallengePolynomialCommitments
      vp.oldBulletproofChallenges

    step = Vector.reifyVector stepProofs \proofs ->
      hashMessagesForNextStepProofPure
        { stepVk: extractWrapVKForStepHash @WrapVkChunks verifier.wrapVK
        , appState: vp.appState
        , proofs
        }

    paddedLen = reflectType (Proxy :: Proxy PaddedLength)

    wrapPadded =
      Array.replicate (paddedLen - Array.length vp.prevWrapBulletproofChallenges)
        dummyIpaChallenges.wrapExpanded
        <> vp.prevWrapBulletproofChallenges

    wrap = Vector.reifyVector wrapPadded \paddedChallenges ->
      hashMessagesForNextWrapProofPureGeneral
        { sg: vp.challengePolynomialCommitment, paddedChallenges }
  in
    { step, wrap }

-- | The wrap proof's kimchi accumulator list, rebuilt from the carried
-- | messages as OCaml `verify.ml` builds `message`: the step message's
-- | `challenge_polynomial_commitments` front-padded with the dummy wrap
-- | `sg`, zipped with the wrap message's expanded old challenges
-- | front-padded with the dummy wrap challenges, to `PaddedLength`
-- | (OCaml: `Vector.extend_front` to `max_proofs_verified`, then
-- | `Wrap_hack.pad_accumulator`; one pad here, since both use the same
-- | dummy accumulator). Each entry is a previous wrap proof's `sg` (a
-- | Pallas point, `StepField` coordinates) with its 15 expanded `WrapField`
-- | challenges — the `prev_challenges` kimchi absorbs into both sponges
-- | and opens at the head of its batch. The list the prover stored in the
-- | proof object is deliberately not read.
wrapAccumulators
  :: Verifier
  -> VerifiableProof
  -> Array { sgX :: StepField, sgY :: StepField, challenges :: Array WrapField }
wrapAccumulators verifier vp =
  let
    paddedLen = reflectType (Proxy :: Proxy PaddedLength)

    padFront :: forall a. a -> Array a -> Array a
    padFront dummy xs = Array.replicate (paddedLen - Array.length xs) dummy <> xs

    sgs = padFront verifier.dummyWrapSg vp.prevChallengePolynomialCommitments
    chals = padFront dummyIpaChallenges.wrapExpanded vp.prevWrapBulletproofChallenges
  in
    Array.zipWith
      (\(AffinePoint sg) ch -> { sgX: sg.x, sgY: sg.y, challenges: Vector.toUnfoldable ch })
      sgs
      chals

-- | Stage 1 for a `VerifiableProof`: reconstruct the expanded wrap deferred
-- | values from the carried minimal skeleton. The prev-proof bp-challenge
-- | width is reified back from the array length (`Vector.reifyVector`).
-- | Shared by `perProof` and `wrapPublicInput`.
expandDv :: Verifier -> VerifiableProof -> WrapDeferredValuesOutput
expandDv verifier vp =
  let
    zetaField = coerce (toFieldPure vp.rawPlonk.zeta (F verifier.stepEndo))

    vanishesOnZkAtZeta = permutationVanishingPolynomial
      { domainLog2: vp.stepDomainLog2
      , zkRows: verifier.stepZkRows
      , pt: zetaField
      }
  in
    Vector.reifyVector vp.oldBulletproofChallenges \oldBpChals ->
      expandDeferredForVerify
        { rawPlonk: vp.rawPlonk
        , rawBulletproofChallenges: vp.rawBulletproofChallenges
        , branchData: vp.branchData
        , spongeDigestBeforeEvaluations: vp.spongeDigestBeforeEvaluations
        , chunkedAllEvals: vp.prevEvalsChunked
        , pEval0Chunks: vp.pEval0Chunks
        , oldBulletproofChallenges: oldBpChals
        , domainLog2: vp.stepDomainLog2
        , zkRows: verifier.stepZkRows
        , srsLengthLog2: verifier.stepSrsLengthLog2
        , generator: domainGenerator vp.stepDomainLog2
        , shifts: domainShifts vp.stepDomainLog2
        , vanishesOnZk: vanishesOnZkAtZeta
        , omegaForLagrange: \_ -> one
        , endo: verifier.stepEndo
        , linearizationPoly: verifier.linearizationPoly
        }

-- | Per-proof verification: stage 1 (expand deferred values), stage 2
-- | (IPA step accumulator check) and stage 3 (message digests), plus
-- | assembly of the wrap proof's kimchi public input and accumulator list.
-- | Stage 4 (the kimchi opening-proof check) is deliberately NOT done here
-- | — `verify` batches it across all proofs into ONE amortized
-- | `batch_verify`. Mirrors OCaml `Verify.verify_heterogenous`
-- | (per-instance expand + accumulator term, then a single batched dlog
-- | check).
perProof
  :: Verifier
  -> VerifiableProof
  -> { accumulatorOk :: Boolean
     , ctx ::
         { proof :: Proof PallasG WrapField
         , publicInput :: Array WrapField
         , prevChallenges :: Array { sgX :: StepField, sgY :: StepField, challenges :: Array WrapField }
         }
     }
perProof verifier vp =
  let
    -- ===== Stage 1: expand deferred values. =====
    dv = expandDv verifier vp

    -- ===== Stage 2: IPA step accumulator check. =====
    -- OCaml `Ipa.Step.accumulator_check`: verify
    -- `compute_sg(expanded bp-chals) == challengePolynomialCommitment`.
    expandedBpChals = Array.fromFoldable $
      map (\c -> coerce (toFieldPure c (F verifier.stepEndo)) :: StepField)
        vp.rawBulletproofChallenges

    computedSg = vestaSrsBPolyCommitmentPoint verifier.vestaSrs expandedBpChals

    accumulatorOk = computedSg == vp.challengePolynomialCommitment

    -- ===== Stage 3: the message digests, from the VK and the state. =====
    digests = messageDigests verifier vp

    -- Wrap proof's kimchi public input and accumulator list. Stage 4 (the
    -- opening-proof check) is intentionally deferred to `verifyBatch`,
    -- which runs it for every proof in ONE amortized
    -- `verifyOpeningProofsBatch`.
    pi = wrapPublicInputOf dv digests.step digests.wrap
  in
    { accumulatorOk
    , ctx: { proof: vp.wrapProof, publicInput: pi, prevChallenges: wrapAccumulators verifier vp }
    }

-- | Verify an array of proofs (all of the same tag).
-- |
-- | Stages 1-2 are independent per proof → run per-proof and
-- | AND-folded (`Array.all`). Stage 3 (the expensive kimchi
-- | opening-proof check) is AMORTIZED: a SINGLE
-- | `verifyOpeningProofsBatch` over every proof's `(wrapVK,
-- | wrapProof, publicInput)` rather than one kimchi verify per
-- | proof. Homogeneous specialization of OCaml
-- | `Verify.verify_heterogenous`'s final `batch_verify`.
verifyBatch
  :: Verifier
  -> Array VerifiableProof
  -> Boolean
verifyBatch v ps =
  let
    rs = map (perProof v) ps
  in
    Array.all _.accumulatorOk rs
      && verifyOpeningProofsBatch v.wrapVK (map _.ctx rs)

-- | Verify a single proof. The public surface: `Verifier → proof → yes/no`.
-- | Defined via `verifyBatch` on a singleton.
verify :: Verifier -> VerifiableProof -> Boolean
verify v p = verifyBatch v [ p ]

-- | Diagnostic: the two verify stages reported separately, so a failure can
-- | be localized to the IPA accumulator check (stage 2) vs the kimchi
-- | opening-proof / public-input check (stage 3).
verifyStages :: Verifier -> VerifiableProof -> { accumulatorOk :: Boolean, kimchiOk :: Boolean }
verifyStages v vp =
  let
    r = perProof v vp
  in
    { accumulatorOk: r.accumulatorOk
    , kimchiOk: verifyOpeningProofsBatch v.wrapVK [ r.ctx ]
    }

-- | Assemble the flat `Array WrapField` that `pallasVerifyOpeningProof`
-- | accepts as its `publicInput`. Exposed as a public helper so tests
-- | can cross-check against the prover's assembled `wrapResult.publicInputs`
-- | without running verification end-to-end.
-- |
-- | Kept on `CompiledProof` for the in-circuit recursive-step advice path
-- | (`Pickles.Prove.Compile`); it just projects via `toVerifiable`.
wrapPublicInput
  :: forall mpv stmtVal
   . Verifier
  -> CompiledProof mpv stmtVal
  -> Array WrapField
wrapPublicInput v cp = wrapPublicInputVP v (toVerifiable cp)

wrapPublicInputVP :: Verifier -> VerifiableProof -> Array WrapField
wrapPublicInputVP v vp =
  let
    digests = messageDigests v vp
  in
    wrapPublicInputOf (expandDv v vp) digests.step digests.wrap

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
