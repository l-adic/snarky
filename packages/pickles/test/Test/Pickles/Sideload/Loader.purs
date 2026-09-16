-- | Loads an OCaml-emitted fixture directory into the canonical
-- | `VerifiableProof` that `Pickles.verify` consumes. There is no
-- | bespoke verifier here.
-- |
-- | A fixture directory is written by an OCaml `dump_*_fixtures.exe`
-- | (for example `mina/src/lib/crypto/pickles/dump_nrr_fixtures/`) and
-- | holds four files:
-- |
-- |   * `vk.serde.json` — kimchi `VerifierIndex`, Rust serde JSON
-- |   * `proof.serde.json` — kimchi wrap `ProverProof`, Rust serde JSON
-- |   * `public_input_skeleton.json` — the Pickles `proof_state`, OCaml
-- |     yojson, decoded here into `OcamlProofWire`
-- |   * `app_statement.json` — the application's public input/output
-- |
-- | The two serde files use the same kimchi crate on both ends. The
-- | yojson `proof_state` has no such shared codec, so the argonaut
-- | decoders below are written against its shape: `Hex64` limb vectors,
-- | scalar-challenge wrappers, big-endian hex, variant tags.
module Test.Pickles.Sideload.Loader
  ( LoadedFixture
  , OcamlProofWire
  , loadFixture
  , decodeHex
  ) where

import Prelude

import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (JsonDecodeError(..), decodeJson, printJsonDecodeError, (.:))
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Array.NonEmpty (NonEmptyArray)
import Data.Array.NonEmpty as NEA
import Data.Bifunctor (lmap)
import Data.Char (toCharCode)
import Data.Either (Either(..), either)
import Data.Maybe (Maybe(..))
import Data.Reflectable (class Reflectable, reflectType)
import Data.String.CodeUnits (charAt)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import JS.BigInt (BigInt)
import JS.BigInt as JsBigInt
import Node.Encoding (Encoding(..))
import Node.FS.Sync (readTextFile)
import Partial.Unsafe (unsafeCrashWith, unsafePartial)
import Pickles (StepField, StepIPARounds, VerifiableProof, Verifier, WrapField, WrapIPARounds, mkVerifier)
import Pickles.DeferredValues (BranchData, PlonkMinimal, ScalarChallenge)
import Pickles.Dummy (stepEndo, wrapEndo)
import Pickles.Linearization.FFI (PointEval)
import Pickles.Sideload (vestaProofFromSerdeJson, vestaVerifierIndexFromSerdeJson)
import Pickles.Types (ChunkedEvals)
import Safe.Coerce (coerce)
import Snarky.Backend.Kimchi.Proof (Proof)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.DSL (F(..))
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField, wrapF)
import Snarky.Circuit.Kimchi.EndoScalar (toFieldPure)
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG, VestaG) as PV
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- BigInt-preserving JSON parser
--------------------------------------------------------------------------------

-- | Re-emit a JSON document with every integer quoted as a string.
-- | OCaml-yojson writes `Int64.t` — the payload of
-- | `Limb_vector.Constant.Hex64.t` — as 19-digit numbers that exceed JS
-- | Number's 53-bit mantissa, so quoting them before argonaut sees them
-- | is what preserves the value. Backed by `json-bigint`.
foreign import parseJsonPreserveBigInts :: String -> String

--------------------------------------------------------------------------------
-- OcamlProofWire
--------------------------------------------------------------------------------

-- | Typed view of the `proof_state` in `public_input_skeleton.json`, the
-- | fixture-format counterpart of the statement skeleton in
-- | `VerifiableProof`.
-- |
-- | The kimchi wrap proof (its own file) and the two message digests
-- | (recomputed by `Pickles.Verify`) are absent. The prev-proof data is
-- | carried: the `prev*` arrays below each have length `mpv`, empty at
-- | `mpv = 0`, and otherwise hold the previous proof's commitments and
-- | bullet challenges from `messages_for_next_{step,wrap}_proof`.
type OcamlProofWire =
  { rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField
  , challengePolynomialCommitment :: AffinePoint WrapField
  , stepDomainLog2 :: Int
  , prevEvalsChunked :: ChunkedEvals StepField
  , pEval0Chunks :: Array StepField
  -- The step challenges run 16 rounds, the wrap challenges 15.
  , prevStepSgs :: Array (AffinePoint StepField)
  , prevStepChalsRaw :: Array (Vector StepIPARounds (ScalarChallenge (F StepField)))
  , prevWrapChalsRaw :: Array (Vector WrapIPARounds (ScalarChallenge (F WrapField)))
  }

-- | Assemble a `VerifiableProof` from an `OcamlProofWire` plus the data
-- | that lives outside the `proof_state` JSON: the serde-decoded kimchi
-- | wrap proof, the application state fields, and the expanded
-- | prev-proof bullet challenges.
ocamlProofWireToVerifiable
  :: { wrapProof :: Proof Pallas.G WrapField
     , appState :: Array StepField
     , oldBulletproofChallenges :: Array (Vector StepIPARounds StepField)
     , prevWrapBulletproofChallenges :: Array (Vector WrapIPARounds WrapField)
     }
  -> OcamlProofWire
  -> VerifiableProof
ocamlProofWireToVerifiable extra w =
  { wrapProof: extra.wrapProof
  , rawPlonk: w.rawPlonk
  , rawBulletproofChallenges: w.rawBulletproofChallenges
  , branchData: w.branchData
  , spongeDigestBeforeEvaluations: w.spongeDigestBeforeEvaluations
  , prevEvalsChunked: w.prevEvalsChunked
  , pEval0Chunks: w.pEval0Chunks
  , appState: extra.appState
  , oldBulletproofChallenges: extra.oldBulletproofChallenges
  , prevChallengePolynomialCommitments: w.prevStepSgs
  , challengePolynomialCommitment: w.challengePolynomialCommitment
  , prevWrapBulletproofChallenges: extra.prevWrapBulletproofChallenges
  , stepDomainLog2: w.stepDomainLog2
  }

--------------------------------------------------------------------------------
-- Fixture surface
--------------------------------------------------------------------------------

-- | One loaded fixture: the kimchi `VerifierIndex` and the JSON it was
-- | decoded from (for round-trip checks), a ready-built `Verifier`, the
-- | canonical `VerifiableProof`, and the decoded application statement.
type LoadedFixture stmtVal =
  { vk :: VerifierIndex Pallas.G WrapField
  , vkJson :: String
  , verifier :: Verifier
  , verifiableProof :: VerifiableProof
  , statement :: stmtVal
  }

-- | Load a fixture directory. The caller supplies the
-- | application-statement codec: `decodeStatement` parses
-- | `app_statement.json`, and `statementToFields` encodes the result as
-- | the `app_state` field vector that
-- | `hashMessagesForNextStepProofPure` absorbs into the
-- | `messagesForNextStepProofDigest`.
-- |
-- | Generic over `max_proofs_verified` and `num_chunks`: the carried
-- | prev-proof data is read from the statement, the message digests and
-- | `oldBulletproofChallenges` are rebuilt from it, and the chunk count
-- | is derived from the dumped `prev_evals`.
loadFixture
  :: forall stmtVal
   . { decodeStatement :: Json -> Either JsonDecodeError stmtVal
     , statementToFields :: stmtVal -> Array StepField
     }
  -> { pallasSrs :: CRS PV.PallasG, vestaSrs :: CRS PV.VestaG }
  -> String
  -> Aff (LoadedFixture stmtVal)
loadFixture cfg sharedSrs dir = do
  vkJson <- liftEffect $ readTextFile UTF8 (dir <> "/vk.serde.json")
  proofSerdeJson <- liftEffect $ readTextFile UTF8 (dir <> "/proof.serde.json")
  wrappingText <- liftEffect $ readTextFile UTF8 (dir <> "/public_input_skeleton.json")
  statementText <- liftEffect $ readTextFile UTF8 (dir <> "/app_statement.json")

  let
    wrappingTextSafe = parseJsonPreserveBigInts wrappingText

    srs = sharedSrs.pallasSrs
    -- The serde form leaves `linearization` and `powers_of_alpha` empty
    -- (`#[serde(skip)]`); conversion to `VerifierIndex` recomputes those
    -- caches from the deserialized commitments.
    vk = vestaVerifierIndexFromSerdeJson vkJson srs

    wireProof = vestaProofFromSerdeJson proofSerdeJson

  statement <- either (liftEffect <<< throw) pure $ parseStatement cfg.decodeStatement statementText
  wire <- either (liftEffect <<< throw) pure $ decodeOcamlProofWire wrappingTextSafe

  let
    vestaSrs = sharedSrs.vestaSrs
    -- The app state comes from `app_statement.json` because the dumped
    -- `messages_for_next_step_proof.app_state` is unusable: the
    -- proof-cache `Repr` erases it to `unit`, so it arrives as null.
    appStateFields = cfg.statementToFields statement

    -- Step challenges expand through the step endo, wrap challenges
    -- through the wrap endo, as in the prover.
    expandStep c = coerce (toFieldPure c (F stepEndo)) :: StepField
    expandWrap c = coerce (toFieldPure c (F wrapEndo)) :: WrapField

    prevStepExpanded :: Array (Vector StepIPARounds StepField)
    prevStepExpanded = map (map expandStep) wire.prevStepChalsRaw

    prevWrapExpanded :: Array (Vector WrapIPARounds WrapField)
    prevWrapExpanded = map (map expandWrap) wire.prevWrapChalsRaw

    verifiableProof = ocamlProofWireToVerifiable
      { wrapProof: wireProof
      , appState: appStateFields
      , oldBulletproofChallenges: prevStepExpanded
      , prevWrapBulletproofChallenges: prevWrapExpanded
      }
      wire

    -- Every chunked evaluation has one entry per chunk, so `zEvals`
    -- carries `num_chunks` in its length.
    stepNumChunks = NEA.length wire.prevEvalsChunked.zEvals

    verifier = mkVerifier
      { wrapVK: vk
      , pallasSrs: sharedSrs.pallasSrs
      , vestaSrs
      , stepNumChunks
      }

  pure { vk, vkJson, verifier, verifiableProof, statement }

--------------------------------------------------------------------------------
-- Hex / int64 / BigInt helpers
--------------------------------------------------------------------------------

-- | Parse a prime-field element from a big-endian `0x`-prefixed hex
-- | string, the fixtures' encoding.
fromHexBe :: forall f. PrimeField f => String -> Either String f
fromHexBe s = case JsBigInt.fromString s of
  Just bi -> Right (fromBigInt bi)
  Nothing -> Left ("fromHexBe: failed to parse " <> s)

decodeHex :: forall f. PrimeField f => Json -> Either JsonDecodeError f
decodeHex j = do
  s <- decodeJson j :: Either JsonDecodeError String
  lmap TypeMismatch (fromHexBe s)

decodeAffinePoint :: forall f. PrimeField f => Json -> Either JsonDecodeError (AffinePoint f)
decodeAffinePoint j = do
  arr <- decodeJson j :: Either JsonDecodeError (Array Json)
  case arr of
    [ x, y ] -> do
      x' <- decodeHex x
      y' <- decodeHex y
      pure (AffinePoint { x: x', y: y' })
    _ -> Left (TypeMismatch ("expected 2-element [x, y] curve point, got " <> show (Array.length arr) <> " elements"))

-- | Decode a JSON int64. `parseJsonPreserveBigInts` quotes values above
-- | ±2^53 and leaves smaller ones as numbers, so String, Number and Int
-- | are tried in that order.
decodeInt64 :: Json -> Either JsonDecodeError BigInt
decodeInt64 j =
  case decodeJson j :: Either JsonDecodeError String of
    Right s -> case JsBigInt.fromString s of
      Just bi -> pure bi
      Nothing -> Left (TypeMismatch ("decodeInt64: failed to parse " <> s))
    Left _ -> case decodeJson j :: Either JsonDecodeError Number of
      Right n -> case JsBigInt.fromNumber n of
        Just bi -> pure bi
        Nothing -> Left
          (TypeMismatch ("decodeInt64: failed to convert number to BigInt: " <> show n))
      Left _ -> case decodeJson j :: Either JsonDecodeError Int of
        Right n -> pure (JsBigInt.fromInt n)
        Left e -> Left e

-- | Combine little-endian `Hex64` limbs into one `BigInt`: index 0 holds
-- | the lowest 64 bits. Limbs arrive as signed int64, so negative values
-- | are reinterpreted as unsigned by adding 2^64.
combineLimbsLE :: Array BigInt -> BigInt
combineLimbsLE limbs =
  let
    twoTo64 = JsBigInt.shl (JsBigInt.fromInt 1) (JsBigInt.fromInt 64)

    toUnsigned :: BigInt -> BigInt
    toUnsigned x = if x < JsBigInt.fromInt 0 then x + twoTo64 else x

    go :: BigInt -> BigInt -> Array BigInt -> BigInt
    go acc shift xs = case Array.uncons xs of
      Nothing -> acc
      Just { head, tail } ->
        go (acc + toUnsigned head * shift) (shift * twoTo64) tail
  in
    go (JsBigInt.fromInt 0) (JsBigInt.fromInt 1) limbs

decodeLimbVec :: Json -> Either JsonDecodeError BigInt
decodeLimbVec j = do
  arr <- decodeJson j :: Either JsonDecodeError (Array Json)
  limbs <- traverse decodeInt64 arr
  pure (combineLimbsLE limbs)

--------------------------------------------------------------------------------
-- Statement parsing
--------------------------------------------------------------------------------

parseStatement
  :: forall stmtVal
   . (Json -> Either JsonDecodeError stmtVal)
  -> String
  -> Either String stmtVal
parseStatement decode raw = do
  json <- jsonParser raw
  lmap show (decode json)

--------------------------------------------------------------------------------
-- OcamlProofWire decoder
--------------------------------------------------------------------------------

decodeOcamlProofWire :: String -> Either String OcamlProofWire
decodeOcamlProofWire raw = do
  json <- jsonParser raw
  lmap printJsonDecodeError (decodeOcamlProofWireJson json)

decodeOcamlProofWireJson :: Json -> Either JsonDecodeError OcamlProofWire
decodeOcamlProofWireJson j = do
  obj <- decodeJson j
  statement <- (obj .: "statement") >>= decodeJson
  proofState <- (statement .: "proof_state") >>= decodeJson
  deferredValues <- (proofState .: "deferred_values") >>= decodeJson

  plonkJ <- deferredValues .: "plonk"
  rawPlonk <- decodePlonkMinimal plonkJ

  bpJ :: Array Json <- deferredValues .: "bulletproof_challenges"
  bpVec <- decodeBulletproofVec bpJ

  branchDataJ <- deferredValues .: "branch_data"
  Tuple branchData stepDomainLog2 <- decodeBranchDataAndLog2 branchDataJ

  spongeJ <- proofState .: "sponge_digest_before_evaluations"
  sponge <- decodeDigestField spongeJ

  msgWrap <- (proofState .: "messages_for_next_wrap_proof") >>= decodeJson
  cpcJ <- msgWrap .: "challenge_polynomial_commitment"
  cpc <- decodeAffinePoint cpcJ :: Either JsonDecodeError (AffinePoint WrapField)

  msgStep <- (statement .: "messages_for_next_step_proof") >>= decodeJson
  prevStepSgsJ :: Array Json <- msgStep .: "challenge_polynomial_commitments"
  prevStepSgs <-
    traverse decodeAffinePoint prevStepSgsJ
      :: Either JsonDecodeError (Array (AffinePoint StepField))
  prevStepObcJ :: Array Json <- msgStep .: "old_bulletproof_challenges"
  prevStepChalsRaw <- traverse
    (\jj -> (decodeJson jj :: Either JsonDecodeError (Array Json)) >>= decodeBulletproofVec)
    prevStepObcJ
  prevWrapObcJ :: Array Json <- msgWrap .: "old_bulletproof_challenges"
  prevWrapChalsRaw <- traverse
    (\jj -> (decodeJson jj :: Either JsonDecodeError (Array Json)) >>= decodeBulletproofVecWrap)
    prevWrapObcJ

  prevEvalsJ <- (obj .: "prev_evals") >>= decodeJson
  prevEvalsChunked <- decodeEvals prevEvalsJ
  let pEval0Chunks = map _.zeta (NEA.toArray prevEvalsChunked.publicEvals)

  pure
    { rawPlonk
    , rawBulletproofChallenges: bpVec
    , branchData
    , spongeDigestBeforeEvaluations: sponge
    , challengePolynomialCommitment: cpc
    , stepDomainLog2
    , prevEvalsChunked
    , pEval0Chunks
    , prevStepSgs
    , prevStepChalsRaw
    , prevWrapChalsRaw
    }

-- | Decode a 128-bit `Hex64` vector to a `BigInt`, in either wire shape:
-- | `{"inner": [int64, int64]}` for a scalar challenge, or a bare
-- | `[int64, int64]`.
decodeChallengeBI :: Json -> Either JsonDecodeError BigInt
decodeChallengeBI j =
  case decodeJson j :: Either JsonDecodeError (Array Json) of
    Right arr -> traverse decodeInt64 arr <#> combineLimbsLE
    Left _ -> do
      obj <- decodeJson j
      innerJ <- obj .: "inner"
      decodeLimbVec innerJ

mkScalarChallenge :: BigInt -> SizedF 128 (F StepField)
mkScalarChallenge bi =
  let
    f = fromBigInt bi :: StepField
    -- A 128-bit value always fits the 255-bit field, discharging
    -- `unsafeFromField`'s `Partial`.
    sized = unsafePartial $ unsafeFromField f :: SizedF 128 StepField
  in
    wrapF sized

decodeChallengeSized :: Json -> Either JsonDecodeError (SizedF 128 (F StepField))
decodeChallengeSized j = mkScalarChallenge <$> decodeChallengeBI j

decodePlonkMinimal :: Json -> Either JsonDecodeError (PlonkMinimal (F StepField))
decodePlonkMinimal j = do
  obj <- decodeJson j
  alphaJ <- obj .: "alpha"
  betaJ <- obj .: "beta"
  gammaJ <- obj .: "gamma"
  zetaJ <- obj .: "zeta"
  alpha <- decodeChallengeSized alphaJ
  beta <- decodeChallengeSized betaJ
  gamma <- decodeChallengeSized gammaJ
  zeta <- decodeChallengeSized zetaJ
  pure { alpha, beta, gamma, zeta }

decodeBulletproofVec
  :: Array Json
  -> Either JsonDecodeError (Vector StepIPARounds (ScalarChallenge (F StepField)))
decodeBulletproofVec arr = do
  vals <- traverse decodeBPChallenge arr
  case Vector.toVector @StepIPARounds vals of
    Just v -> pure v
    Nothing -> Left (TypeMismatch ("expected 16 bulletproof challenges, got " <> show (Array.length vals)))

decodeBPChallenge :: Json -> Either JsonDecodeError (SizedF 128 (F StepField))
decodeBPChallenge j = do
  obj <- decodeJson j
  prech <- obj .: "prechallenge"
  decodeChallengeSized prech

-- | `WrapField` counterpart of `mkScalarChallenge`, for the 15-round
-- | `messages_for_next_wrap_proof.old_bulletproof_challenges`. Same wire
-- | shape, the other field.
mkScalarChallengeWrap :: BigInt -> SizedF 128 (F WrapField)
mkScalarChallengeWrap bi =
  let
    f = fromBigInt bi :: WrapField
    sized = unsafePartial $ unsafeFromField f :: SizedF 128 WrapField
  in
    wrapF sized

decodeBPChallengeWrap :: Json -> Either JsonDecodeError (SizedF 128 (F WrapField))
decodeBPChallengeWrap j = do
  obj <- decodeJson j
  prech <- obj .: "prechallenge"
  mkScalarChallengeWrap <$> decodeChallengeBI prech

decodeBulletproofVecWrap
  :: Array Json
  -> Either JsonDecodeError (Vector WrapIPARounds (ScalarChallenge (F WrapField)))
decodeBulletproofVecWrap arr = do
  vals <- traverse decodeBPChallengeWrap arr
  case Vector.toVector @WrapIPARounds vals of
    Just v -> pure v
    Nothing -> Left (TypeMismatch ("expected 15 wrap bulletproof challenges, got " <> show (Array.length vals)))

-- | Decode `proof_state.sponge_digest_before_evaluations`, a 256-bit
-- | digest carried as four `Hex64` limbs.
decodeDigestField :: Json -> Either JsonDecodeError StepField
decodeDigestField j = do
  bi <- decodeLimbVec j
  pure (fromBigInt bi)

decodeBranchDataAndLog2
  :: Json
  -> Either JsonDecodeError (Tuple (BranchData StepField Boolean) Int)
decodeBranchDataAndLog2 j = do
  obj <- decodeJson j
  pvJ <- obj .: "proofs_verified"
  proofsVerifiedMask <- decodeProofsVerified pvJ
  domLog2J <- obj .: "domain_log2"
  domLog2 <- decodeOcamlByte domLog2J
  pure $ Tuple
    { domainLog2: fromBigInt (JsBigInt.fromInt domLog2) :: StepField
    , proofsVerifiedMask
    }
    domLog2

-- | Decode the variant `N0 | N1 | N2`, wire-encoded as a single-element
-- | array `["N0"]`, into the `Vector 2 Boolean` mask.
-- |
-- | The mask is the reversed one `revOnesVector` builds —
-- | N0 → `[F, F]`, N1 → `[F, T]`, N2 → `[T, T]` — not the prefix mask.
-- | `packBranchDataWrap` packs it as `m0 + 2·m1`, giving N0 → 0,
-- | N1 → 2, N2 → 3, which is what the wrap public input carries. The
-- | two conventions agree on N0 and N2 and differ on N1.
decodeProofsVerified :: Json -> Either JsonDecodeError (Vector 2 Boolean)
decodeProofsVerified j = do
  arr :: Array Json <- decodeJson j
  case arr of
    [ tagJ ] -> do
      tag <- decodeJson tagJ :: Either JsonDecodeError String
      case tag of
        "N0" -> pure (mkMask false false)
        "N1" -> pure (mkMask false true)
        "N2" -> pure (mkMask true true)
        _ -> Left (TypeMismatch ("expected N0|N1|N2, got " <> tag))
    _ -> Left (TypeMismatch "expected single-element variant tag")
  where
  mkMask m0 m1 = case Vector.toVector @2 [ m0, m1 ] of
    Just v -> v
    Nothing -> unsafeCrashWith "mkMask: impossible"

-- | A single-byte `Hex64` — here `domain_log2` — is wire-encoded as a
-- | one-character string whose char code is the byte.
decodeOcamlByte :: Json -> Either JsonDecodeError Int
decodeOcamlByte j = do
  s <- decodeJson j :: Either JsonDecodeError String
  case charAt 0 s of
    Just c -> pure (toCharCode c)
    Nothing -> Left (TypeMismatch ("expected single-char byte string, got empty"))

--------------------------------------------------------------------------------
-- Evals decoder
--------------------------------------------------------------------------------

-- | Decode `prev_evals` from `public_input_skeleton.json`: a flat
-- | `[zeta, omega_zeta]` `public_input`, then the kimchi
-- | `proof_evaluations` — 6 always-on selectors, `z`, 15 `w`, 15
-- | `coefficients` and 6 `s`.
decodeEvals :: Json -> Either JsonDecodeError (ChunkedEvals StepField)
decodeEvals j = do
  obj <- decodeJson j
  ftJ <- obj .: "ft_eval1"
  ftEval1 <- decodeHex ftJ :: Either JsonDecodeError StepField

  evalsObj <- (obj .: "evals") >>= decodeJson
  publicJ <- evalsObj .: "public_input"
  -- The dumped public input is flat, i.e. a single chunk.
  publicEvalsFlat <- decodePointEvalFlat publicJ
  let publicEvals = NEA.singleton publicEvalsFlat

  innerEvals <- (evalsObj .: "evals") >>= decodeJson

  zJ <- innerEvals .: "z"
  zEvals <- decodePointEvalChunked zJ

  wJArr :: Array Json <- innerEvals .: "w"
  wEvals <- traverse decodePointEvalChunked wJArr
  witnessEvals <- toFixedVec @15 "w" wEvals

  cArr :: Array Json <- innerEvals .: "coefficients"
  cEvals <- traverse decodePointEvalChunked cArr
  coeffEvals <- toFixedVec @15 "coefficients" cEvals

  sArr :: Array Json <- innerEvals .: "s"
  sEvals <- traverse decodePointEvalChunked sArr
  sigmaEvals <- toFixedVec @6 "s" sEvals

  genJ <- innerEvals .: "generic_selector"
  posJ <- innerEvals .: "poseidon_selector"
  caJ <- innerEvals .: "complete_add_selector"
  mulJ <- innerEvals .: "mul_selector"
  emulJ <- innerEvals .: "emul_selector"
  esJ <- innerEvals .: "endomul_scalar_selector"
  gen <- decodePointEvalChunked genJ
  pos <- decodePointEvalChunked posJ
  ca <- decodePointEvalChunked caJ
  mul <- decodePointEvalChunked mulJ
  emul <- decodePointEvalChunked emulJ
  es <- decodePointEvalChunked esJ
  indexEvals <- toFixedVec @6 "indexEvals" [ gen, pos, ca, mul, emul, es ]

  pure { ftEval1, publicEvals, zEvals, indexEvals, witnessEvals, coeffEvals, sigmaEvals }

-- | Decode a flat point eval `[zeta_hex, omega_zeta_hex]`, the shape of
-- | `prev_evals.evals.public_input`.
decodePointEvalFlat :: Json -> Either JsonDecodeError (PointEval StepField)
decodePointEvalFlat j = do
  arr <- decodeJson j :: Either JsonDecodeError (Array Json)
  case arr of
    [ zetaJ, omegaJ ] -> do
      zeta <- decodeHex zetaJ
      omegaTimesZeta <- decodeHex omegaJ
      pure { zeta, omegaTimesZeta }
    _ -> Left (TypeMismatch ("decodePointEvalFlat: expected 2-elem array"))

-- | Decode a chunked point eval `[[zeta_hex…], [omega_zeta_hex…]]`, the
-- | shape of the kimchi `proof_evaluations` inside
-- | `prev_evals.evals.evals`. Both inner arrays must have length
-- | `num_chunks`; one `PointEval` is returned per chunk.
decodePointEvalChunked
  :: Json -> Either JsonDecodeError (NonEmptyArray (PointEval StepField))
decodePointEvalChunked j = do
  arr <- decodeJson j :: Either JsonDecodeError (Array Json)
  case arr of
    [ zetaArrJ, omegaArrJ ] -> do
      zetaArr :: Array Json <- decodeJson zetaArrJ
      omegaArr :: Array Json <- decodeJson omegaArrJ
      when (Array.length zetaArr /= Array.length omegaArr) $ Left
        ( TypeMismatch
            ( "decodePointEvalChunked: zeta/omega chunk count mismatch ("
                <> show (Array.length zetaArr)
                <> "/"
                <> show (Array.length omegaArr)
                <> ")"
            )
        )
      case NEA.fromArray zetaArr of
        Nothing ->
          Left (TypeMismatch "decodePointEvalChunked: empty chunks array")
        Just zetaNea -> do
          let
            mkChunk zJ oJ = do
              zeta <- decodeHex zJ
              omegaTimesZeta <- decodeHex oJ
              pure { zeta, omegaTimesZeta }
          -- Safe: the two lengths were checked equal above.
          let pairs = Array.zip (NEA.toArray zetaNea) omegaArr
          chunksArr <- traverse (\(Tuple z o) -> mkChunk z o) pairs
          case NEA.fromArray chunksArr of
            Just nea -> pure nea
            Nothing ->
              Left (TypeMismatch "decodePointEvalChunked: lost non-empty invariant")
    _ -> Left (TypeMismatch ("decodePointEvalChunked: expected [zeta_chunks, omega_chunks]"))

toFixedVec :: forall @n a. Reflectable n Int => String -> Array a -> Either JsonDecodeError (Vector n a)
toFixedVec label arr =
  case Vector.toVector @n arr of
    Just v -> pure v
    Nothing -> Left
      ( TypeMismatch
          ( label <> ": expected " <> show (reflectType (Proxy @n))
              <> " elements, got "
              <> show (Array.length arr)
          )
      )
