-- | JSON codecs for out-of-circuit wrap verification: a
-- | `VerifiableProof` (what `Pickles.Verify.verify` consumes) and a
-- | `Verifier` (the constants it needs), for shipping a finished proof
-- | to a client and verifying it there.
-- |
-- | The wrap kimchi proof and the wrap VK round-trip through the Rust
-- | serde codecs; the statement skeleton around them has none, and goes
-- | through simple-json's leaf instances. `linearizationPoly` and the
-- | two SRSes are never serialized — the first is the constant
-- | `Linearization.pallas`, the second are supplied to `decodeVerifier`.
module Pickles.Prove.Codecs
  ( encodeVerifiableProof
  , decodeVerifiableProof
  , encodeVerifier
  , decodeVerifier
  ) where

import Prelude

import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Either (Either(..))
import Data.Maybe (maybe)
import Data.Traversable (traverse)
import Data.Vector (Vector)
import Foreign (ForeignError(..), MultipleErrors)
import Pickles.DeferredValues (BranchData, PlonkMinimal, ScalarChallenge)
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (PointEval)
import Pickles.Types (ChunkedEvals, StepIPARounds, WrapIPARounds)
import Pickles.Verify (VerifiableProof, Verifier, dummyWrapSgOf)
import Simple.JSON (readJSON, writeJSON)
import Snarky.Backend.Kimchi.Proof (vestaProofFromSerdeJson, vestaProofToSerdeJson, vestaVerifierIndexFromSerdeJson, vestaVerifierIndexToSerdeJson)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Wire form of `ChunkedEvals`: each polynomial's per-chunk
-- | `NonEmptyArray` becomes a plain `Array`, simple-json having no
-- | `NonEmptyArray` codec.
type ChunkedEvalsWire f =
  { publicEvals :: Array (PointEval f)
  , witnessEvals :: Vector 15 (Array (PointEval f))
  , coeffEvals :: Vector 15 (Array (PointEval f))
  , zEvals :: Array (PointEval f)
  , sigmaEvals :: Vector 6 (Array (PointEval f))
  , indexEvals :: Vector 6 (Array (PointEval f))
  , ftEval1 :: f
  }

-- | Wire form of a `VerifiableProof`: the wrap proof becomes its
-- | serde-JSON string and the chunked evals lose their
-- | `NonEmptyArray`s; every other field is unchanged.
type VerifiableProofWire =
  { wrapProof :: String
  , rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField
  , prevEvalsChunked :: ChunkedEvalsWire StepField
  , pEval0Chunks :: Array StepField
  , appState :: Array StepField
  , oldBulletproofChallenges :: Array (Vector StepIPARounds StepField)
  , prevChallengePolynomialCommitments :: Array (AffinePoint StepField)
  , challengePolynomialCommitment :: AffinePoint WrapField
  , prevWrapBulletproofChallenges :: Array (Vector WrapIPARounds WrapField)
  , stepDomainLog2 :: Int
  }

-- | Wire form of a `Verifier`: the wrap VK becomes its serde-JSON
-- | string, and the step-domain constants serialize directly.
type VerifierWire =
  { wrapVK :: String
  , stepZkRows :: Int
  , stepSrsLengthLog2 :: Int
  , stepEndo :: StepField
  }

toWireEvals :: forall f. ChunkedEvals f -> ChunkedEvalsWire f
toWireEvals e =
  { ftEval1: e.ftEval1
  , publicEvals: NEA.toArray e.publicEvals
  , zEvals: NEA.toArray e.zEvals
  , indexEvals: map NEA.toArray e.indexEvals
  , witnessEvals: map NEA.toArray e.witnessEvals
  , coeffEvals: map NEA.toArray e.coeffEvals
  , sigmaEvals: map NEA.toArray e.sigmaEvals
  }

nea :: forall a. Array a -> Either MultipleErrors (NonEmptyArray a)
nea = maybe (Left (pure (ForeignError "ChunkedEvals: empty chunk array"))) Right <<< NEA.fromArray

fromWireEvals :: forall f. ChunkedEvalsWire f -> Either MultipleErrors (ChunkedEvals f)
fromWireEvals w = do
  publicEvals <- nea w.publicEvals
  zEvals <- nea w.zEvals
  indexEvals <- traverse nea w.indexEvals
  witnessEvals <- traverse nea w.witnessEvals
  coeffEvals <- traverse nea w.coeffEvals
  sigmaEvals <- traverse nea w.sigmaEvals
  pure
    { ftEval1: w.ftEval1
    , publicEvals
    , zEvals
    , indexEvals
    , witnessEvals
    , coeffEvals
    , sigmaEvals
    }

toWire :: VerifiableProof -> VerifiableProofWire
toWire vp =
  { wrapProof: vestaProofToSerdeJson vp.wrapProof
  , rawPlonk: vp.rawPlonk
  , rawBulletproofChallenges: vp.rawBulletproofChallenges
  , branchData: vp.branchData
  , spongeDigestBeforeEvaluations: vp.spongeDigestBeforeEvaluations
  , prevEvalsChunked: toWireEvals vp.prevEvalsChunked
  , pEval0Chunks: vp.pEval0Chunks
  , appState: vp.appState
  , oldBulletproofChallenges: vp.oldBulletproofChallenges
  , prevChallengePolynomialCommitments: vp.prevChallengePolynomialCommitments
  , challengePolynomialCommitment: vp.challengePolynomialCommitment
  , prevWrapBulletproofChallenges: vp.prevWrapBulletproofChallenges
  , stepDomainLog2: vp.stepDomainLog2
  }

fromWire :: VerifiableProofWire -> Either MultipleErrors VerifiableProof
fromWire w = do
  prevEvalsChunked <- fromWireEvals w.prevEvalsChunked
  pure
    { wrapProof: vestaProofFromSerdeJson w.wrapProof
    , rawPlonk: w.rawPlonk
    , rawBulletproofChallenges: w.rawBulletproofChallenges
    , branchData: w.branchData
    , spongeDigestBeforeEvaluations: w.spongeDigestBeforeEvaluations
    , prevEvalsChunked
    , pEval0Chunks: w.pEval0Chunks
    , appState: w.appState
    , oldBulletproofChallenges: w.oldBulletproofChallenges
    , prevChallengePolynomialCommitments: w.prevChallengePolynomialCommitments
    , challengePolynomialCommitment: w.challengePolynomialCommitment
    , prevWrapBulletproofChallenges: w.prevWrapBulletproofChallenges
    , stepDomainLog2: w.stepDomainLog2
    }

encodeVerifiableProof :: VerifiableProof -> String
encodeVerifiableProof = writeJSON <<< toWire

decodeVerifiableProof :: String -> Either MultipleErrors VerifiableProof
decodeVerifiableProof s = (readJSON s :: Either MultipleErrors VerifiableProofWire) >>= fromWire

encodeVerifier :: Verifier -> String
encodeVerifier v = writeJSON
  ( { wrapVK: vestaVerifierIndexToSerdeJson v.wrapVK
    , stepZkRows: v.stepZkRows
    , stepSrsLengthLog2: v.stepSrsLengthLog2
    , stepEndo: v.stepEndo
    } :: VerifierWire
  )

-- | The wrap VK is rehydrated with the caller's Pallas SRS; the Vesta
-- | SRS is stored as is.
decodeVerifier
  :: { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG }
  -> String
  -> Either MultipleErrors Verifier
decodeVerifier srs s = do
  w :: VerifierWire <- readJSON s
  pure
    { wrapVK: vestaVerifierIndexFromSerdeJson w.wrapVK srs.pallasSrs
    , vestaSrs: srs.vestaSrs
    , stepZkRows: w.stepZkRows
    , stepSrsLengthLog2: w.stepSrsLengthLog2
    , stepEndo: w.stepEndo
    , linearizationPoly: Linearization.pallas
    , dummyWrapSg: dummyWrapSgOf srs.pallasSrs
    }
