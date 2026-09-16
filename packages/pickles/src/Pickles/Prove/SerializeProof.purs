-- | Full-proof (de)serialization for the recursion/worker-transport
-- | path: `SerializableCompiledProof` carries everything a
-- | `CompiledProof` holds, so a worker can rebuild a mergeable
-- | `InductivePrev` from one value, where the verify-only codecs in
-- | `Pickles.Prove.Codecs` carry only what verification needs.
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
import Pickles.Prove.Codecs (decodeVerifiableProof, encodeVerifiableProof)
import Pickles.Step.Dummy (baseCaseDummies, computeDummySgValues)
import Pickles.Types (Evals, PaddedLength, StepIPARounds, WrapIPARounds)
import Pickles.Verify (CompiledProof(..), CompiledProofWidthData(..), SomeCompiledProofWidthData, VerifiableProof, mkSomeCompiledProofWidthData, toVerifiable)
import Simple.JSON (class ReadForeign, class WriteForeign, readJSON, writeJSON)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | The flat superset of `VerifiableProof`: everything in a
-- | `CompiledProof` that the verify-only projection drops — the
-- | application `statement`, the single-value `prevEvals`, and the two
-- | per-prev message vectors a recursive prev needs.
-- |
-- | `VerifiableProof` already carries the other half of each message,
-- | as `oldBulletproofChallenges` and `challengePolynomialCommitment`,
-- | so only the dropped halves live here. The vectors are width-erased
-- | to `Array`; the per-rule prev width is reified back on reconstruct.
type SerializableCompiledProof stmtVal =
  { verifiable :: VerifiableProof
  , statement :: stmtVal
  , prevEvals :: Evals StepField
  , messagesForNextStepProof ::
      { challengePolynomialCommitments :: Array (AffinePoint StepField) }
  , messagesForNextWrapProof ::
      { oldBulletproofChallenges :: Array (Vector WrapIPARounds WrapField) }
  }

-- | The front-padding dummies `mkSomeCompiledProofWidthData` needs to
-- | lift the `Vector width` per-prev fields to their `Vector
-- | PaddedLength` padded views — the same program constants the prover
-- | packs at the `CompiledProof` construction site.
type WidthDummies =
  { dummyOldBp :: Vector StepIPARounds StepField
  , dummyMsgWrap :: Vector WrapIPARounds WrapField
  , dummyChalPolyComm :: AffinePoint StepField
  }

-- | The front-padding dummies for a given SRS pair, independent of any
-- | program's `mpvMax`.
mkWidthDummies :: CRS PallasG -> CRS VestaG -> WidthDummies
mkWidthDummies pallasSrs vestaSrs =
  let
    dummySgsMax = computeDummySgValues (baseCaseDummies { maxProofsVerified: 0 }) pallasSrs vestaSrs
  in
    { dummyOldBp: dummyIpaChallenges.stepExpanded
    , dummyMsgWrap: dummyIpaChallenges.wrapExpanded
    , dummyChalPolyComm: dummySgsMax.ipa.wrap.sg
    }

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

-- | The mergeable `CompiledProof` a `SerializableCompiledProof`
-- | describes, with the `widthData` existential rebuilt from the
-- | carried array lengths and the supplied dummies. `mpv` is a phantom
-- | index, so the result unifies with whatever program consumes it.
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
      , appState: vp.appState
      , widthData:
          rebuildWidthData dummies vp.oldBulletproofChallenges
            vp.prevWrapBulletproofChallenges
            vp.prevChallengePolynomialCommitments
      , stepDomainLog2: vp.stepDomainLog2
      }

-- | Rebuild the `widthData` existential, reifying the prev width from
-- | the (equal) array lengths. `PaddedLength = 2`, so the width is one
-- | of 0/1/2 — a finite dispatch.
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

-- | JSON wire form of `SerializableCompiledProof`: `verifiable` is
-- | embedded as a nested JSON string via `Pickles.Prove.Codecs`, and
-- | the rest serializes through its leaf instances.
type SerializableCompiledProofWire stmtVal =
  { verifiable :: String
  , statement :: stmtVal
  , prevEvals :: Evals StepField
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

encodeCompiledProof
  :: forall mpv stmtVal
   . WriteForeign stmtVal
  => CompiledProof mpv stmtVal
  -> String
encodeCompiledProof = writeJSON <<< toWireSCP <<< toSerializableCompiledProof

-- | Parse a full `CompiledProof` from JSON. Takes any record carrying
-- | `pallasSrs`/`vestaSrs` — the app `Env` does — and builds the
-- | front-padding `WidthDummies` itself, so the caller never handles
-- | them.
decodeCompiledProof
  :: forall mpv stmtVal r
   . ReadForeign stmtVal
  => { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG | r }
  -> String
  -> Either MultipleErrors (CompiledProof mpv stmtVal)
decodeCompiledProof srs s = do
  w :: SerializableCompiledProofWire stmtVal <- readJSON s
  scp <- fromWireSCP w
  pure (reconstructCompiledProof (mkWidthDummies srs.pallasSrs srs.vestaSrs) scp)
