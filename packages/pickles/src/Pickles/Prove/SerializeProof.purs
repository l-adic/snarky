-- | Full-proof (de)serialization for the recursion/worker-transport path.
-- |
-- | A `CompiledProof` is the prover's internal proof record — the thing a
-- | merge/recursive rule needs as an `InductivePrev`. Unlike
-- | `Pickles.Verify.VerifiableProof` (the verify-only projection that the
-- | OCaml-compatible codecs round-trip), a `CompiledProof` carries the
-- | recursive bookkeeping a *prev* needs: the per-prev `msgWrapChallenges`
-- | and `outerStepChalPolyComms` hidden behind the `widthData` existential,
-- | plus the application `statement` and the collapsed `prevEvals`.
-- |
-- | `SerializableCompiledProof` is the flat, self-describing superset of
-- | `VerifiableProof` that carries exactly those extra pieces, so a worker
-- | can reconstruct a complete, mergeable `CompiledProof` from a single
-- | value. This is **separate from** and does **not** touch the
-- | OCaml-compatible `VerifiableProof`/`Verifier` codecs in
-- | `Pickles.Prove.Codecs` — it is purely our internal transport form.
-- |
-- | The `widthData` existential is rebuilt with `mkSomeCompiledProofWidthData`
-- | (reifying the per-rule prev width back from the carried array lengths);
-- | the front-padding dummies are program constants supplied by the caller
-- | (the same `dummyIpaChallenges` / dummy wrap-sg the prover uses).
module Pickles.Prove.SerializeProof
  ( SerializableCompiledProof
  , WidthDummies
  , mkWidthDummies
  , toSerializableCompiledProof
  , reconstructCompiledProof
  , encodeCompiledProof
  , decodeCompiledProof
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either)
import Data.Exists (runExists)
import Data.Maybe (fromJust)
import Data.Reflectable (class Reflectable)
import Data.Vector (Vector)
import Data.Vector as Vector
import Foreign (MultipleErrors)
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Field (StepField, WrapField)
import Pickles.PlonkChecks (AllEvals)
import Pickles.Prove.Codecs (decodeVerifiableProof, encodeVerifiableProof)
import Pickles.Step.Dummy (baseCaseDummies, computeDummySgValues)
import Pickles.Types (PaddedLength, StepIPARounds, WrapIPARounds)
import Pickles.Verify (CompiledProof(..), CompiledProofWidthData(..), SomeCompiledProofWidthData, VerifiableProof, mkSomeCompiledProofWidthData, toVerifiable)
import Simple.JSON (class ReadForeign, class WriteForeign, readJSON, writeJSON)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | The flat, self-describing superset of `VerifiableProof`: everything in a
-- | `CompiledProof` that the verify-only projection drops — the application
-- | `statement`, the single-value `prevEvals`, and the two per-prev
-- | `messages_for_next_*_proof` vectors a recursive prev needs.
-- |
-- | The vector fields follow OCaml's `messages_for_next_{step,wrap}_proof`
-- | naming (camelCased). `VerifiableProof` already carries the other half of
-- | each message — `messages_for_next_step_proof.old_bulletproof_challenges`
-- | (its `oldBulletproofChallenges`) and
-- | `messages_for_next_wrap_proof.challenge_polynomial_commitment` (its
-- | `challengePolynomialCommitment`) — so only the dropped halves live here.
-- | The vectors are width-erased to `Array` (the per-rule prev width is reified
-- | back on reconstruct).
type SerializableCompiledProof stmtVal =
  { verifiable :: VerifiableProof
  , statement :: stmtVal
  , prevEvals :: AllEvals StepField
  , messagesForNextStepProof ::
      { challengePolynomialCommitments :: Array (AffinePoint StepField) }
  , messagesForNextWrapProof ::
      { oldBulletproofChallenges :: Array (Vector WrapIPARounds WrapField) }
  }

-- | The front-padding dummies `mkSomeCompiledProofWidthData` needs to lift the
-- | `Vector width` per-prev fields to the `Vector PaddedLength` padded views.
-- | These are program constants: `dummyIpaChallenges.stepExpanded`,
-- | `dummyIpaChallenges.wrapExpanded`, and the dummy wrap sg in step field
-- | (`computeDummySgValues … .ipa.wrap.sg`) — the same values the prover packs
-- | at the `CompiledProof` construction site.
type WidthDummies =
  { dummyOldBp :: Vector StepIPARounds StepField
  , dummyMsgWrap :: Vector WrapIPARounds WrapField
  , dummyChalPolyComm :: AffinePoint StepField
  }

-- | Build the front-padding `WidthDummies` from the SRSes — program constants
-- | (the prover's `dummyIpaChallenges` bp-challenge stacks and the
-- | `maxProofsVerified: 0` dummy wrap sg), independent of any program's mpvMax.
-- | Any caller of `reconstructCompiledProof`/`decodeCompiledProof` needs these.
mkWidthDummies :: CRS PallasG -> CRS VestaG -> WidthDummies
mkWidthDummies pallasSrs vestaSrs =
  let
    dummySgsMax = computeDummySgValues (baseCaseDummies { maxProofsVerified: 0 }) pallasSrs vestaSrs
  in
    { dummyOldBp: dummyIpaChallenges.stepExpanded
    , dummyMsgWrap: dummyIpaChallenges.wrapExpanded
    , dummyChalPolyComm: dummySgsMax.ipa.wrap.sg
    }

-- | Project a `CompiledProof` to its self-describing serializable form.
toSerializableCompiledProof
  :: forall mpv stmtVal
   . CompiledProof mpv stmtVal
  -> SerializableCompiledProof stmtVal
toSerializableCompiledProof cp@(CompiledProof rec) =
  runExists
    ( \(CompiledProofWidthData wd) ->
        { verifiable: toVerifiable cp
        , statement: rec.statement
        , prevEvals: rec.prevEvals
        , messagesForNextStepProof:
            { challengePolynomialCommitments: Array.fromFoldable wd.outerStepChalPolyComms }
        , messagesForNextWrapProof:
            { oldBulletproofChallenges: Array.fromFoldable wd.msgWrapChallenges }
        }
    )
    rec.widthData

-- | Reassemble a complete, mergeable `CompiledProof` from its serializable
-- | form. The result is pinned to `PaddedLength` (the program's `mpvMax`); the
-- | per-rule prev width is reified from the carried array lengths and the
-- | `widthData` existential rebuilt with the supplied program dummies.
-- | `mpv` (the program `mpvMax`) is a phantom index on `CompiledProof`, so the
-- | result unifies with whatever the consuming program expects.
reconstructCompiledProof
  :: forall mpv stmtVal
   . WidthDummies
  -> SerializableCompiledProof stmtVal
  -> CompiledProof mpv stmtVal
reconstructCompiledProof dummies scp =
  let
    vp = scp.verifiable
  in
    CompiledProof
      { statement: scp.statement
      , wrapProof: vp.wrapProof
      , rawPlonk: vp.rawPlonk
      , rawBulletproofChallenges: vp.rawBulletproofChallenges
      , branchData: vp.branchData
      , spongeDigestBeforeEvaluations: vp.spongeDigestBeforeEvaluations
      , prevEvals: scp.prevEvals
      , prevEvalsChunked: vp.prevEvalsChunked
      , pEval0Chunks: vp.pEval0Chunks
      , challengePolynomialCommitment: vp.challengePolynomialCommitment
      , messagesForNextStepProofDigest: vp.messagesForNextStepProofDigest
      , messagesForNextWrapProofDigest: vp.messagesForNextWrapProofDigest
      , widthData:
          rebuildWidthData dummies vp.oldBulletproofChallenges
            scp.messagesForNextWrapProof.oldBulletproofChallenges
            scp.messagesForNextStepProof.challengePolynomialCommitments
      , stepDomainLog2: vp.stepDomainLog2
      }

-- | Rebuild the `widthData` existential, reifying the prev width from the
-- | (equal) array lengths. `PaddedLength = 2`, so the width is one of 0/1/2 —
-- | a finite dispatch into `mkSomeCompiledProofWidthData @width @pad`.
rebuildWidthData
  :: WidthDummies
  -> Array (Vector StepIPARounds StepField)
  -> Array (Vector WrapIPARounds WrapField)
  -> Array (AffinePoint StepField)
  -> SomeCompiledProofWidthData
rebuildWidthData dummies oldBp msgWrap outerSg =
  case Array.length oldBp of
    0 ->
      mkSomeCompiledProofWidthData @0 @PaddedLength
        { oldBulletproofChallenges: Vector.nil
        , msgWrapChallenges: Vector.nil
        , outerStepChalPolyComms: Vector.nil
        , dummyOldBp: dummies.dummyOldBp
        , dummyMsgWrap: dummies.dummyMsgWrap
        , dummyChalPolyComm: dummies.dummyChalPolyComm
        }
    1 ->
      mkSomeCompiledProofWidthData @1 @1
        { oldBulletproofChallenges: toVec @1 oldBp
        , msgWrapChallenges: toVec @1 msgWrap
        , outerStepChalPolyComms: toVec @1 outerSg
        , dummyOldBp: dummies.dummyOldBp
        , dummyMsgWrap: dummies.dummyMsgWrap
        , dummyChalPolyComm: dummies.dummyChalPolyComm
        }
    2 ->
      mkSomeCompiledProofWidthData @2 @0
        { oldBulletproofChallenges: toVec @2 oldBp
        , msgWrapChallenges: toVec @2 msgWrap
        , outerStepChalPolyComms: toVec @2 outerSg
        , dummyOldBp: dummies.dummyOldBp
        , dummyMsgWrap: dummies.dummyMsgWrap
        , dummyChalPolyComm: dummies.dummyChalPolyComm
        }
    n ->
      unsafeCrashWith
        ( "reconstructCompiledProof: prev width " <> show n
            <> " exceeds PaddedLength=2"
        )

toVec :: forall @n a. Reflectable n Int => Array a -> Vector n a
toVec arr = unsafePartial fromJust (Vector.toVector @n arr)

-- | JSON wire form of `SerializableCompiledProof`: the `verifiable` field is
-- | embedded as a nested JSON string via `Pickles.Prove.Codecs` (the same way
-- | its own `wrapProof` is a nested serde string — it carries the kimchi proof +
-- | chunked evals). The rest — the application `statement` (generic), the
-- | single-eval `prevEvals`, and the two `messages_for_next_*` vectors —
-- | serialize directly via their leaf `WriteForeign`/`ReadForeign` instances
-- | (fields as hex, `AffinePoint`, `Vector`).
type SerializableCompiledProofWire stmtVal =
  { verifiable :: String
  , statement :: stmtVal
  , prevEvals :: AllEvals StepField
  , messagesForNextStepProof ::
      { challengePolynomialCommitments :: Array (AffinePoint StepField) }
  , messagesForNextWrapProof ::
      { oldBulletproofChallenges :: Array (Vector WrapIPARounds WrapField) }
  }

toWireSCP :: forall stmtVal. SerializableCompiledProof stmtVal -> SerializableCompiledProofWire stmtVal
toWireSCP scp = scp { verifiable = encodeVerifiableProof scp.verifiable }

fromWireSCP
  :: forall stmtVal
   . SerializableCompiledProofWire stmtVal
  -> Either MultipleErrors (SerializableCompiledProof stmtVal)
fromWireSCP w = do
  verifiable <- decodeVerifiableProof w.verifiable
  pure (w { verifiable = verifiable })

-- | Serialize a full `CompiledProof` to JSON for worker/recursion transport.
-- | Generic over the application `statement`, which the caller's
-- | `WriteForeign` instance encodes.
encodeCompiledProof
  :: forall mpv stmtVal
   . WriteForeign stmtVal
  => CompiledProof mpv stmtVal
  -> String
encodeCompiledProof = writeJSON <<< toWireSCP <<< toSerializableCompiledProof

-- | Parse a full `CompiledProof` from JSON. As with `reconstructCompiledProof`,
-- | the caller supplies the program's front-padding `WidthDummies`; `mpv` (the
-- | program `mpvMax`) is a phantom index, so the result unifies with whatever
-- | program consumes it.
decodeCompiledProof
  :: forall mpv stmtVal
   . ReadForeign stmtVal
  => WidthDummies
  -> String
  -> Either MultipleErrors (CompiledProof mpv stmtVal)
decodeCompiledProof dummies s = do
  w :: SerializableCompiledProofWire stmtVal <- readJSON s
  scp <- fromWireSCP w
  pure (reconstructCompiledProof dummies scp)
