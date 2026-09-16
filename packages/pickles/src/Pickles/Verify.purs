-- | Top-level out-of-circuit Pickles verifier.
-- |
-- | A `Verifier` is what you ship to a client, a `CompiledProof` is
-- | what a prover hands over, and `verify` says whether that proof is
-- | valid for its claimed statement. The split is along what varies: a
-- | `Verifier` holds only per-tag constants — wrap VK, Vesta SRS, step
-- | domain metadata — so it carries no prover state.
-- |
-- | `perProof` runs the per-proof work: expand the carried deferred
-- | values, check the IPA step accumulator, and recompute both message
-- | digests. The kimchi opening-proof check is left to `verifyBatch`,
-- | which amortizes it across every proof in one call.
module Pickles.Verify
  ( CompiledProof(..)
  , CompiledProofWidthData(..)
  , SomeCompiledProofWidthData
  , mkSomeCompiledProofWidthData
  , Verifier
  , PaddedAccumulators
  , PrevProofData
  , prevProofDataOf
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
  , wrapPublicInputVP
  ) where

import Prelude

import Data.Array as Array
import Data.Exists (Exists, mkExists, runExists)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Vector (Vector)
import Data.Vector as Vector
import Pickles.Constants (zkRowsForNumChunks)
import Pickles.DeferredValues (BranchData, PlonkMinimal, ScalarChallenge)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (domainGenerator, domainShifts)
import Pickles.Linearization.Types (LinearizationPoly)
import Pickles.Prove.Pure.Verify (expandDeferredForVerify)
import Pickles.Prove.Pure.Wrap (WrapDeferredValuesOutput, assembleWrapMainInput)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Types (ChunkedEvals, Evals, PaddedLength, StepIPARounds, WrapIPARounds, WrapVkChunks)
import Pickles.VerificationKey (extractWrapVKForStepHash)
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

-- | The constants one tag's proofs are verified against. Shippable on
-- | its own: the wrap VK, the Vesta SRS, and the step-domain constants
-- | read off the compiled step circuit.
type Verifier =
  { wrapVK :: VerifierIndex PallasG WrapField
  -- | Step SRS, for the accumulator-check MSM.
  , vestaSrs :: CRS VestaG
  -- | Kimchi's `zk_rows` for the step circuit
  -- | (`Pickles.Constants.zkRowsForNumChunks`).
  , stepZkRows :: Int
  -- | Step SRS size log2 (= `StepIPARounds` = 16). A constant of the
  -- | Pasta cycle, not a per-circuit value: every step proof's IPA
  -- | rounds are bounded by the SRS size.
  , stepSrsLengthLog2 :: Int
  -- | Step-field scalar endo coefficient (= `endoScalar @StepField`).
  , stepEndo :: StepField
  -- | Tick linearization polynomial (= `Pickles.Linearization.pallas`).
  , linearizationPoly :: LinearizationPoly StepField
  -- | The accumulator a padding slot carries; `wrapAccumulators` pads
  -- | with it.
  , dummyWrapSg :: AffinePoint StepField
  }

-- | The commitment every dummy-padded accumulator slot carries: the
-- | challenge-polynomial commitment of the dummy wrap challenges on the
-- | Pallas SRS.
dummyWrapSgOf :: CRS PallasG -> AffinePoint StepField
dummyWrapSgOf pallasSrs =
  pallasSrsBPolyCommitmentPoint pallasSrs (Vector.toUnfoldable dummyIpaChallenges.wrapExpanded)

-- | Build a `Verifier` from the minimum a caller has: a compiled wrap
-- | VK, the two SRSes, and the step `numChunks` that drives `zk_rows`.
-- | Everything else — endo, linearization, the dummy accumulator — is
-- | fixed by the Pickles setup. The step domain log2 is not among
-- | them: it varies per proof, so `expandDv` rebuilds the generator and
-- | shifts from each `VerifiableProof`'s `stepDomainLog2`.
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

-- | The fields of a `CompiledProof` sized by the rule's actual prev
-- | step-proof count, rather than by the proof system's
-- | `max_proofs_verified`. They share one `width` because they all hold
-- | per-prev-step-proof data.
-- |
-- | `CompiledProof` holds this behind `Exists`, so `width` does not
-- | appear in its type.
data CompiledProofWidthData :: Int -> Type
data CompiledProofWidthData width = CompiledProofWidthData
  { -- `reflectType (Proxy @width)`, stored rather than reflected on
    -- demand: PS's `Exists` does not carry type-class instances across
    -- the existential boundary, so a consumer inside `runExists` has no
    -- `Reflectable width Int`.
    width :: Int

  -- The inner step proof's prev-proof bp challenges, carried by the
  -- wrap proof's `messages_for_next_step_proof`.
  , oldBulletproofChallenges :: Vector width (Vector StepIPARounds StepField)

  -- Per-prev wrap-side bp challenges, as this proof hashed them into
  -- `messagesForNextWrapProofDigest`.
  , msgWrapChallenges :: Vector width (Vector WrapIPARounds WrapField)

  -- Per-prev outer-step `sg` values, as used for the real slots'
  -- `sgX`/`sgY` when this proof's wrap proof was generated.
  , outerStepChalPolyComms :: Vector width (AffinePoint StepField)

  -- The three above, front-padded with their matching dummy.
  --
  -- Padding is done by the producer and stored, not recomputed by
  -- consumers: inside `runExists` the `width` is rigid, so no consumer
  -- can form the `Add pad width PaddedLength` that padding needs.
  -- `mkSomeCompiledProofWidthData` has it, its `width` being concrete.
  , oldBulletproofChallengesPadded :: Vector PaddedLength (Vector StepIPARounds StepField)
  , msgWrapChallengesPadded :: Vector PaddedLength (Vector WrapIPARounds WrapField)
  , outerStepChalPolyCommsPadded :: Vector PaddedLength (AffinePoint StepField)
  }

-- | `CompiledProofWidthData` with its `width` hidden; consumers
-- | `runExists` to recover it.
type SomeCompiledProofWidthData = Exists CompiledProofWidthData

-- | Build a `SomeCompiledProofWidthData`, computing the padded views
-- | from the unpadded ones while `width` is still concrete, then hiding
-- | it.
mkSomeCompiledProofWidthData
  :: forall @width @pad
   . Reflectable width Int
  => Reflectable pad Int
  => Add pad width PaddedLength
  => { oldBulletproofChallenges :: Vector width (Vector StepIPARounds StepField)
     , msgWrapChallenges :: Vector width (Vector WrapIPARounds WrapField)
     , outerStepChalPolyComms :: Vector width (AffinePoint StepField)
     -- One front-padding dummy per padded view, filling the `pad` slots
     -- prepended to each `Vector width X`.
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

-- | What a prover hands over: everything needed to verify one proof
-- | except the per-tag constants, which live in `Verifier`.
-- |
-- | `mpv` is the proof system's outer `max_proofs_verified`, which pins
-- | the proof's `Tag _ mpv` and so its system identity. The fields
-- | sized by the rule's own prev count are hidden in `widthData`.
newtype CompiledProof :: Int -> Type -> Type
newtype CompiledProof mpv stmtVal = CompiledProof
  { -- The rule's application input and output. The production prover
    -- uses `StatementIO inputVal outputVal`, whose output a consumer
    -- reaches as `(unwrap cp.statement).output`.
    statement :: stmtVal

  , wrapProof :: Proof PallasG WrapField

  -- The wrap proof's minimal statement skeleton, which `expandDv`
  -- expands. The scalar challenges are raw 128-bit values; the endo
  -- expansion happens inside the verifier.
  , rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField

  -- The inner step proof's evaluations, carried by the wrap proof.
  --
  -- `prevEvalsChunked` is the authoritative form, one entry per chunk,
  -- and `combinedInnerProductBatchChunked` consumes it directly.
  -- `prevEvals` is the same data Horner-recombined at the step proof's
  -- oracle zeta/zetaw, for the recursive-step `wrapPrevEvals` and
  -- `stepAdvicePrevEvals` plumbing in `Pickles.Prove.Step`, which takes
  -- a single eval per polynomial.
  , prevEvals :: Evals StepField
  , prevEvalsChunked :: ChunkedEvals StepField
  , pEval0Chunks :: Array StepField

  -- The inner step proof's IPA opening `sg`, which the accumulator
  -- check requires to equal `compute_sg(rawBulletproofChallenges)` on
  -- the step SRS.
  , challengePolynomialCommitment :: AffinePoint WrapField

  -- The application state exactly as the step circuit absorbed it into
  -- the `messages_for_next_step_proof` digest: the rule's public input
  -- fields followed by its public output fields (`Pickles.Step.Main`'s
  -- `hashAppFields`). The verifier recomputes that digest from these
  -- fields and the real wrap VK; no digest is carried.
  , appState :: Array StepField

  , widthData :: SomeCompiledProofWidthData

  -- The step domain log2 of this proof's branch. A `Verifier` is shared
  -- across a tag's branches, so it cannot hold this; expanding the
  -- deferred values rebuilds the domain generator and shifts from it.
  , stepDomainLog2 :: Int
  }

-- | The minimal serializable proof an out-of-circuit verifier consumes:
-- | the wrap kimchi proof, the carried statement skeleton, and the raw
-- | messages both digests are recomputed from. What a `CompiledProof`
-- | carries beyond that — the typed `statement`, the collapsed
-- | `prevEvals` — verification does not read. The per-rule prev width
-- | is erased to plain `Array`s, the three prev-indexed ones aligned
-- | slot by slot.
-- |
-- | Neither message digest is a field. A prover-supplied digest would
-- | let the prover choose which wrap VK and which application state the
-- | chain is bound to, so `messageDigests` recomputes both.
type VerifiableProof =
  { wrapProof :: Proof PallasG WrapField
  , rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField
  , prevEvalsChunked :: ChunkedEvals StepField
  , pEval0Chunks :: Array StepField
  -- The claimed application state, as `CompiledProof.appState`.
  , appState :: Array StepField
  -- `messages_for_next_step_proof`: per prev proof, its expanded
  -- 16-round step challenges and its challenge-polynomial commitment.
  , oldBulletproofChallenges :: Array (Vector StepIPARounds StepField)
  , prevChallengePolynomialCommitments :: Array (AffinePoint StepField)
  -- `messages_for_next_wrap_proof`: this proof's inner step opening
  -- `sg`, which is also the accumulator-check target, and, per prev
  -- proof, its expanded 15-round wrap challenges.
  , challengePolynomialCommitment :: AffinePoint WrapField
  , prevWrapBulletproofChallenges :: Array (Vector WrapIPARounds WrapField)
  , stepDomainLog2 :: Int
  }

-- | A `CompiledProof` as the `VerifiableProof` the verifier wants, with
-- | the per-rule width existential opened and erased.
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

-- | A previous proof as the recursive prover needs it: the erased
-- | proof, the constants it is judged against, and the two views
-- | `toVerifiable` drops.
-- |
-- | The step circuit finishes the previous step proof's deferred
-- | arithmetic, so building its advice means replaying the verifier's
-- | computation natively to get the witness. Both `verifier` and
-- | `proof` are here because `expandDeferredForVerify` and
-- | `wrapPublicInputVP` each read from both.
-- |
-- | `prevEvals` is the chunk-collapsed form, which `VerifiableProof`
-- | does not keep and the recursive plumbing in `Pickles.Prove.Step`
-- | consumes; `padded` holds the views verification itself never wants,
-- | since it folds over unpadded accumulators.
type PrevProofData =
  { proof :: VerifiableProof
  , verifier :: Verifier
  , prevEvals :: Evals StepField
  , padded :: PaddedAccumulators
  }

-- | The three per-prev accumulators front-padded to `PaddedLength`. The
-- | `Padded` suffix stays on the field names because `VerifiableProof`
-- | carries unpadded fields of the same base names and the two are not
-- | interchangeable: padding changes the challenges digest and the
-- | combined inner product.
type PaddedAccumulators =
  { oldBulletproofChallengesPadded :: Vector PaddedLength (Vector StepIPARounds StepField)
  , msgWrapChallengesPadded :: Vector PaddedLength (Vector WrapIPARounds WrapField)
  , outerStepChalPolyCommsPadded :: Vector PaddedLength (AffinePoint StepField)
  }

-- | Build the recursive prover's view of a previous proof. Opens the
-- | width existential once, here, instead of inside the per-slot advice
-- | logic.
prevProofDataOf
  :: forall mpv stmtVal
   . Verifier
  -> CompiledProof mpv stmtVal
  -> PrevProofData
prevProofDataOf verifier cp@(CompiledProof p) =
  { proof: toVerifiable cp
  , verifier
  , prevEvals: p.prevEvals
  , padded:
      runExists
        ( \(CompiledProofWidthData wd) ->
            { oldBulletproofChallengesPadded: wd.oldBulletproofChallengesPadded
            , msgWrapChallengesPadded: wd.msgWrapChallengesPadded
            , outerStepChalPolyCommsPadded: wd.outerStepChalPolyCommsPadded
            }
        )
        p.widthData
  }

-- | The wrap statement's two message digests, recomputed from the
-- | verifier's wrap VK and the proof's carried raw messages.
-- |
-- | This is what binds a proof to its key and its statement. The step
-- | digest absorbs the verifier's own wrap VK commitments, the claimed
-- | `appState`, and each prev proof's `(sg, expanded step challenges)`;
-- | the wrap digest absorbs this proof's inner `sg` and the prev wrap
-- | challenges front-padded with dummies to `PaddedLength`. Both land
-- | in the wrap public input, so a proof whose step circuit hashed a
-- | different key or state fails the kimchi check.
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
-- | messages: each previous wrap proof's `sg` — a Pallas point, so
-- | `StepField` coordinates — with its 15 expanded `WrapField`
-- | challenges, both front-padded to `PaddedLength` with their dummy.
-- | Kimchi absorbs these into both sponges and opens them at the head
-- | of its batch.
-- |
-- | The list the prover stored in the proof object is not read: it
-- | would let the prover open the wrap proof at accumulators unrelated
-- | to the `sg` it hashed.
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

-- | The expanded wrap deferred values, reconstructed from the proof's
-- | carried minimal skeleton. The prev-proof bp-challenge width is
-- | reified back from the array length.
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
        , chunkedEvals: vp.prevEvalsChunked
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

-- | Everything one proof needs on its own: the accumulator check's
-- | verdict, plus the wrap proof's kimchi public input and accumulator
-- | list. The kimchi opening-proof check is not run here;
-- | `verifyBatch` amortizes it across every proof in one call.
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
    dv = expandDv verifier vp

    -- The accumulator check: `compute_sg` of the expanded bp challenges
    -- must be the carried `challengePolynomialCommitment`. This is the
    -- IPA work Pickles defers through the recursion.
    expandedBpChals = Array.fromFoldable $
      map (\c -> coerce (toFieldPure c (F verifier.stepEndo)) :: StepField)
        vp.rawBulletproofChallenges

    computedSg = vestaSrsBPolyCommitmentPoint verifier.vestaSrs expandedBpChals

    accumulatorOk = computedSg == vp.challengePolynomialCommitment

    digests = messageDigests verifier vp

    pi = wrapPublicInputOf dv digests.step digests.wrap
  in
    { accumulatorOk
    , ctx: { proof: vp.wrapProof, publicInput: pi, prevChallenges: wrapAccumulators verifier vp }
    }

-- | Whether every proof in an array, all of one tag, is valid. The
-- | per-proof work is independent and AND-folded; the expensive kimchi
-- | opening-proof check runs once, as a single
-- | `verifyOpeningProofsBatch` over all of them.
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

-- | Whether one proof is valid for its claimed statement.
verify :: Verifier -> VerifiableProof -> Boolean
verify v p = verifyBatch v [ p ]

-- | The same verdict as `verify`, split so a failure can be localized
-- | to the IPA accumulator check or to the kimchi opening-proof and
-- | public-input check.
verifyStages :: Verifier -> VerifiableProof -> { accumulatorOk :: Boolean, kimchiOk :: Boolean }
verifyStages v vp =
  let
    r = perProof v vp
  in
    { accumulatorOk: r.accumulatorOk
    , kimchiOk: verifyOpeningProofsBatch v.wrapVK [ r.ctx ]
    }

-- | The flat public input the kimchi verifier takes for this proof.
-- | Public so that tests can cross-check it against the prover's own
-- | `wrapResult.publicInputs` without running verification end to end,
-- | and so the recursive-step advice path in `Pickles.Prove.Compile`
-- | can ask for it from a `CompiledProof` directly.
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

-- | Expanded deferred values and both message digests, flattened into
-- | the kimchi public-input array through `Wrap.StatementPacked`.
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
