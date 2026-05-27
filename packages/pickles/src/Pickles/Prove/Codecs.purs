-- | JSON codecs for OUT-OF-CIRCUIT wrap verification: a `VerifiableProof`
-- | (what `Pickles.Verify.verify` consumes) and a `Verifier` (the per-tag
-- | constants it needs). This is purely for shipping a finished proof +
-- | verifier to a client and verifying it again — it has nothing to do with
-- | in-circuit verification.
-- |
-- | Design:
-- |
-- |  * The big object — the wrap kimchi proof — round-trips through the Rust
-- |    `serde_json` codec (`vestaProof{To,From}SerdeJson`), and the wrap VK
-- |    through `vestaVerifierIndex{To,From}SerdeJson`. We use the underlying
-- |    serde serializers wherever they exist.
-- |  * Everything else is the carried statement skeleton — pickles-level
-- |    field elements with no Rust serde codec. Those serialize through
-- |    simple-json using the leaf `ReadForeign`/`WriteForeign` instances on
-- |    `VestaScalarField`/`PallasScalarField` (hex), `F`, `SizedF`, and
-- |    `Vector`, so the records fall out for free.
-- |  * Some data is NEVER serialized but RECONSTRUCTED at decode time: the
-- |    `Verifier`'s `linearizationPoly` is the fixed `Linearization.pallas`
-- |    constant, and the two SRSes are too large to embed — they are passed
-- |    into `decodeVerifier`. (The expanded deferred values are likewise
-- |    reconstructed, but that happens inside `verify`, not here.)
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
import Pickles.Field (StepField, WrapField)
import Pickles.Linearization (pallas) as Linearization
import Pickles.Linearization.FFI (PointEval)
import Pickles.PlonkChecks (ChunkedAllEvals)
import Pickles.Types (StepIPARounds)
import Pickles.Verify (VerifiableProof, Verifier)
import Pickles.Verify.Types (BranchData, PlonkMinimal, ScalarChallenge)
import Simple.JSON (readJSON, writeJSON)
import Snarky.Backend.Kimchi.Proof (vestaProofFromSerdeJson, vestaProofToSerdeJson, vestaVerifierIndexFromSerdeJson, vestaVerifierIndexToSerdeJson)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.DSL (F)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Data.EllipticCurve (AffinePoint)

-- | Wire form of the chunked evals: the only difference from `ChunkedAllEvals`
-- | is that each polynomial's per-chunk `NonEmptyArray` becomes a plain
-- | `Array` (simple-json has no `NonEmptyArray` codec). `PointEval` is the
-- | record `{ zeta, omegaTimesZeta }`, so it serializes directly.
type ChunkedAllEvalsWire f =
  { ftEval1 :: f
  , publicEvals :: Array (PointEval f)
  , zEvals :: Array (PointEval f)
  , indexEvals :: Vector 6 (Array (PointEval f))
  , witnessEvals :: Vector 15 (Array (PointEval f))
  , coeffEvals :: Vector 15 (Array (PointEval f))
  , sigmaEvals :: Vector 6 (Array (PointEval f))
  }

-- | Wire form of a `VerifiableProof`: the wrap proof becomes its serde-JSON
-- | string, the chunked evals lose their `NonEmptyArray`s, and every other
-- | field is identical (and serialized via the leaf instances).
type VerifiableProofWire =
  { wrapProof :: String
  , rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField
  , prevEvalsChunked :: ChunkedAllEvalsWire StepField
  , pEval0Chunks :: Array StepField
  , oldBulletproofChallenges :: Array (Vector StepIPARounds StepField)
  , challengePolynomialCommitment :: AffinePoint WrapField
  , messagesForNextStepProofDigest :: StepField
  , messagesForNextWrapProofDigest :: WrapField
  , stepDomainLog2 :: Int
  }

-- | Wire form of a `Verifier`: the wrap VK becomes its serde-JSON string; the
-- | small step-domain constants serialize directly. `linearizationPoly` and
-- | the two SRSes are NOT here — they're reconstructed/supplied on decode.
type VerifierWire =
  { wrapVK :: String
  , stepZkRows :: Int
  , stepSrsLengthLog2 :: Int
  , stepEndo :: StepField
  }

toWireEvals :: forall f. ChunkedAllEvals f -> ChunkedAllEvalsWire f
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
nea = maybe (Left (pure (ForeignError "ChunkedAllEvals: empty chunk array"))) Right <<< NEA.fromArray

fromWireEvals :: forall f. ChunkedAllEvalsWire f -> Either MultipleErrors (ChunkedAllEvals f)
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
  , oldBulletproofChallenges: vp.oldBulletproofChallenges
  , challengePolynomialCommitment: vp.challengePolynomialCommitment
  , messagesForNextStepProofDigest: vp.messagesForNextStepProofDigest
  , messagesForNextWrapProofDigest: vp.messagesForNextWrapProofDigest
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
    , oldBulletproofChallenges: w.oldBulletproofChallenges
    , challengePolynomialCommitment: w.challengePolynomialCommitment
    , messagesForNextStepProofDigest: w.messagesForNextStepProofDigest
    , messagesForNextWrapProofDigest: w.messagesForNextWrapProofDigest
    , stepDomainLog2: w.stepDomainLog2
    }

-- | Serialize a `VerifiableProof` to JSON.
encodeVerifiableProof :: VerifiableProof -> String
encodeVerifiableProof = writeJSON <<< toWire

-- | Parse a `VerifiableProof` from JSON.
decodeVerifiableProof :: String -> Either MultipleErrors VerifiableProof
decodeVerifiableProof s = (readJSON s :: Either MultipleErrors VerifiableProofWire) >>= fromWire

-- | Serialize a `Verifier` to JSON. The wrap VK goes through serde; the SRSes
-- | and the (constant) linearization polynomial are dropped.
encodeVerifier :: Verifier -> String
encodeVerifier v = writeJSON
  ( { wrapVK: vestaVerifierIndexToSerdeJson v.wrapVK
    , stepZkRows: v.stepZkRows
    , stepSrsLengthLog2: v.stepSrsLengthLog2
    , stepEndo: v.stepEndo
    } :: VerifierWire
  )

-- | Parse a `Verifier` from JSON. The caller supplies the two SRSes (the wrap
-- | VK is rehydrated with the Pallas/wrap SRS; the Vesta/step SRS is stored as
-- | is); `linearizationPoly` is reconstructed from the fixed constant.
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
    }
