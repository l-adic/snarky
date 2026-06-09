-- | Test-only loader for OCaml-emitted Pickles side-load fixtures.
-- |
-- | Reads the files written by an OCaml-side `dump_*_fixtures.exe` tool
-- | (see `mina/src/lib/crypto/pickles/dump_nrr_fixtures/` for the NRR
-- | example):
-- |   * `vk.serde.json`     — kimchi `VerifierIndex` Rust serde JSON
-- |   * `proof.serde.json`  — kimchi wrap `ProverProof` Rust serde JSON
-- |   * `public_input_skeleton.json`     — the Pickles `proof_state` (OCaml yojson)
-- |   * `app_statement.json`    — the application's public input/output
-- |
-- | Architecture (mirrors `Pickles.Prove.Codecs`):
-- |
-- |   * The kimchi wrap proof + VK round-trip through the **Rust serde**
-- |     codecs (`vestaProofFromSerdeJson`, `vestaVerifierIndexFromSerdeJson`)
-- |     — same kimchi crate on both ends, language-neutral.
-- |   * OCaml's `proof_state` is yojson with its own shape (Hex64 limb
-- |     vectors, scalar-challenge wrappers, BE hex, variant tags). We parse
-- |     it into a typed `OcamlProofWire` (the argonaut decoders below — the
-- |     OCaml-format adapter), then `ocamlProofWireToVerifiable` converts it
-- |     to the canonical `Pickles.Verify.VerifiableProof`.
-- |   * Verification is then the canonical `Pickles.Verify.verify` — there is
-- |     no bespoke verifier here.
-- |
-- | OCaml-yojson encodes 128-bit `Hex64` values as JSON int64 pairs that
-- | exceed JS Number precision (2^53). We use `json-bigint` via
-- | `parseJsonPreserveBigInts` to re-emit int64s as JSON strings before
-- | argonaut decoding.
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
import Pickles (PaddedLength, StepField, StepIPARounds, VerifiableProof, Verifier, WrapField, WrapIPARounds, mkVerifier)
import Pickles.Dummy (dummyIpaChallenges, stepEndo, wrapEndo)
import Pickles.Linearization.FFI (PointEval)
import Pickles.PlonkChecks (ChunkedAllEvals)
import Pickles.Prove.Step (extractWrapVKForStepHash)
import Pickles.Sideload (vestaProofFromSerdeJson, vestaVerifierIndexFromSerdeJson)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Verify.Types (BranchData, PlonkMinimal, ScalarChallenge)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
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

-- | Re-emit a JSON document with all integer values stored as JSON strings,
-- | preserving int64 precision. Backed by `json-bigint` with
-- | `{ storeAsString: true }`. OCaml-yojson `[@@deriving yojson]` on
-- | `Int64.t` (the underlying type of `Limb_vector.Constant.Hex64.t`)
-- | emits 19-digit numbers that exceed JS Number's 53-bit mantissa; this
-- | helper sidesteps that by quoting them before argonaut sees them.
foreign import parseJsonPreserveBigInts :: String -> String

--------------------------------------------------------------------------------
-- OcamlProofWire: the typed parse of OCaml's `proof_state` yojson
--------------------------------------------------------------------------------

-- | Typed view of the Pickles `proof_state` an OCaml `dump_*_fixtures` tool
-- | emits in `public_input_skeleton.json`. This is the OCaml-format counterpart of the
-- | carried statement skeleton in `Pickles.Verify.VerifiableProof`; the
-- | bespoke argonaut decoders below are its codec (OCaml limb vectors /
-- | scalar-challenge wrappers / BE hex → PS field elements).
-- |
-- | It deliberately omits the kimchi wrap proof (separate `proof.serde.json`,
-- | Rust serde) and the two message digests (recomputed). The prev-proof
-- | data IS carried (the `mpv`-many `prev*` arrays below) — at mpv=0 (NRR /
-- | chunks2) they're empty, at mpv≥1 (SimpleChain, N2) they hold the carried
-- | previous-proof commitments + bullet challenges from
-- | `messages_for_next_{step,wrap}_proof`. `loadFixture` expands them.
type OcamlProofWire =
  { rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField
  , challengePolynomialCommitment :: AffinePoint WrapField
  , stepDomainLog2 :: Int
  , prevEvalsChunked :: ChunkedAllEvals StepField
  , pEval0Chunks :: Array StepField
  -- mpv-many previous-proof data, carried in the proof's own statement.
  -- `prevStepSgs` + `prevStepChalsRaw` come from
  -- `messages_for_next_step_proof` (16-round, step IPA); `prevWrapChalsRaw`
  -- from `messages_for_next_wrap_proof` (15-round, wrap IPA). Each is
  -- length `mpv` (0, 1 or 2).
  , prevStepSgs :: Array (AffinePoint StepField)
  , prevStepChalsRaw :: Array (Vector StepIPARounds (ScalarChallenge (F StepField)))
  , prevWrapChalsRaw :: Array (Vector WrapIPARounds (ScalarChallenge (F WrapField)))
  }

-- | Assemble a canonical `VerifiableProof` from an `OcamlProofWire` plus the
-- | data that lives outside OCaml's proof_state JSON: the serde-decoded
-- | kimchi wrap proof, the two recomputed message digests, and the
-- | prev-proof bp-challenges (`[]` for mpv=0). Verification is then the
-- | ordinary `Pickles.Verify.verify`.
ocamlProofWireToVerifiable
  :: { wrapProof :: Proof Pallas.G WrapField
     , messagesForNextStepProofDigest :: StepField
     , messagesForNextWrapProofDigest :: WrapField
     , oldBulletproofChallenges :: Array (Vector StepIPARounds StepField)
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
  , oldBulletproofChallenges: extra.oldBulletproofChallenges
  , challengePolynomialCommitment: w.challengePolynomialCommitment
  , messagesForNextStepProofDigest: extra.messagesForNextStepProofDigest
  , messagesForNextWrapProofDigest: extra.messagesForNextWrapProofDigest
  , stepDomainLog2: w.stepDomainLog2
  }

--------------------------------------------------------------------------------
-- Fixture surface
--------------------------------------------------------------------------------

-- | An OCaml-loaded NRR fixture: the kimchi `VerifierIndex` (+ its original
-- | JSON for round-trip checks), a ready-built `Verifier`, and a canonical
-- | `VerifiableProof` (verify via `Pickles.Verify.verify`).
type LoadedFixture stmtVal =
  { vk :: VerifierIndex Pallas.G WrapField
  , vkJson :: String
  , verifier :: Verifier
  , verifiableProof :: VerifiableProof
  , statement :: stmtVal
  }

-- | Generic fixture loader. Caller supplies the application-statement codec:
-- |   * `decodeStatement`: parse `app_statement.json` into the statement value
-- |   * `statementToFields`: encode the statement value as its field-element
-- |     vector — OCaml's `Statement_value.to_field_elements`, i.e. the
-- |     `app_state` absorbed by `hashMessagesForNextStepProofPure` into the
-- |     `messagesForNextStepProofDigest`.
-- |
-- | Generic over max_proofs_verified: the carried prev-proof data
-- | (`prevStepSgs` / `prev*ChalsRaw`, length `mpv`) is read from the
-- | statement and the two message digests + `oldBulletproofChallenges` are
-- | rebuilt from it. mpv=0 (NRR / chunks2) → empty prev data (all-dummy wrap
-- | padding, no step proofs); mpv≥1 (SimpleChain) → the real prev proofs.
-- | num_chunks is derived from the dumped `prev_evals`, so chunked proofs
-- | load too.
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
    -- Re-encode int64s as JSON strings so argonaut doesn't lose precision.
    wrappingTextSafe = parseJsonPreserveBigInts wrappingText

    srs = sharedSrs.pallasSrs
    -- Deserialize → hydrate. The serde codec leaves `linearization` and
    -- `powers_of_alpha` empty (`#[serde(skip)]`); hydration is automatic on
    -- conversion (`From<NapiPlonkVerifierIndex> for VerifierIndex` recomputes
    -- those caches from the deserialized optional-comm shape).
    vk = vestaVerifierIndexFromSerdeJson vkJson srs

    -- Kimchi proof via the same Rust serde codec OCaml wrote it with.
    wireProof = vestaProofFromSerdeJson proofSerdeJson

  statement <- either (liftEffect <<< throw) pure $ parseStatement cfg.decodeStatement statementText
  wire <- either (liftEffect <<< throw) pure $ decodeOcamlProofWire wrappingTextSafe

  let
    vestaSrs = sharedSrs.vestaSrs
    -- appState = the app's statement fields. The step-message digest absorbs
    -- the proof's own app_state, which equals the application statement
    -- (`app_statement.json`). The dumped `messages_for_next_step_proof.app_state`
    -- is unusable: the proof-cache `Repr` erases it to `unit` (→ JSON null).
    appStateFields = cfg.statementToFields statement

    wrapVkStep = extractWrapVKForStepHash @1 vk

    -- Expand the carried prev-proof bullet challenges (mpv-many; empty at
    -- mpv=0). Step challenges (16-round) via the step endo, wrap challenges
    -- (15-round) via the wrap endo — same `toFieldPure ... endo` the prover
    -- uses (Prove.Pure.Step / Compile).
    expandStep c = coerce (toFieldPure c (F stepEndo)) :: StepField
    expandWrap c = coerce (toFieldPure c (F wrapEndo)) :: WrapField

    prevStepExpanded :: Array (Vector StepIPARounds StepField)
    prevStepExpanded = map (map expandStep) wire.prevStepChalsRaw

    prevWrapExpanded :: Array (Vector WrapIPARounds WrapField)
    prevWrapExpanded = map (map expandWrap) wire.prevWrapChalsRaw

    -- messages_for_next_step_proof digest: one {sg, expandedBpChallenges} per
    -- prev proof. `reifyVector` handles any mpv width (0/1/2).
    stepProofs = Array.zipWith
      (\sg expandedBpChallenges -> { sg, expandedBpChallenges })
      wire.prevStepSgs
      prevStepExpanded

    msgStep = Vector.reifyVector stepProofs \proofs ->
      hashMessagesForNextStepProofPure
        { stepVk: wrapVkStep, appState: appStateFields, proofs }

    -- messages_for_next_wrap_proof digest: front-pad the prev wrap challenges
    -- with dummies up to PaddedLength (OCaml `Wrap_hack.pad_challenges`
    -- prepends dummies — wrap_hack.ml:19-28). At mpv=0 this is all dummies.
    paddedLen = reflectType (Proxy :: Proxy PaddedLength)
    msgWrapPaddedArr =
      Array.replicate (paddedLen - Array.length prevWrapExpanded)
        dummyIpaChallenges.wrapExpanded
        <> prevWrapExpanded

    msgWrap = Vector.reifyVector msgWrapPaddedArr \paddedChallenges ->
      hashMessagesForNextWrapProofPureGeneral
        { sg: wire.challengePolynomialCommitment, paddedChallenges }

    verifiableProof = ocamlProofWireToVerifiable
      { wrapProof: wireProof
      , messagesForNextStepProofDigest: msgStep
      , messagesForNextWrapProofDigest: msgWrap
      , oldBulletproofChallenges: prevStepExpanded
      }
      wire

    -- num_chunks is carried by the dumped prev_evals: every chunked
    -- evaluation (here `z`) has exactly one entry per chunk, so the chunk
    -- count is the length of that vector. (For the current NRR/SimpleChain
    -- fixtures this is 1; deriving it keeps the loader correct for chunked
    -- proofs without a hardcoded assumption.)
    stepNumChunks = NEA.length wire.prevEvalsChunked.zEvals

    verifier = mkVerifier
      { wrapVK: vk
      , vestaSrs
      , stepNumChunks
      }

  pure { vk, vkJson, verifier, verifiableProof, statement }

--------------------------------------------------------------------------------
-- Hex / int64 / BigInt helpers
--------------------------------------------------------------------------------

-- | Parse a big-endian hex string (e.g. `"0x2B7F..."`) into a prime-field
-- | element. OCaml's `Pasta_field.to_yojson` emits BE hex with `0x` prefix.
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

-- | Decode a JSON int64. After `parseJsonPreserveBigInts` rewrites
-- | numbers above ±2^53 as strings, smaller integers stay as JSON
-- | numbers. We try three forms in order: String, Number, Int.
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

-- | Combine an array of little-endian `Int64.t` limbs into one `BigInt`.
-- | OCaml's `Limb_vector.Constant.Hex64.t Vector_n.t` stores the lowest 64
-- | bits at index 0. Each limb is signed int64 in OCaml-yojson; we
-- | reinterpret negative values as unsigned (add 2^64) before combining.
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
-- OcamlProofWire decoder (the OCaml proof_state yojson adapter)
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

  -- Previous-proof data carried in this proof's own statement (mpv-many;
  -- empty at mpv=0). `messages_for_next_step_proof` carries the prev sgs +
  -- 16-round step bullet challenges; `messages_for_next_wrap_proof` carries
  -- the 15-round wrap bullet challenges (for the wrap-message digest).
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

  -- prev_evals — natively chunked. `pEval0Chunks` collects the zeta
  -- evaluation of every public-input chunk (sized by num_chunks).
  prevEvalsJ <- (obj .: "prev_evals") >>= decodeJson
  prevEvalsChunked <- decodeAllEvals prevEvalsJ
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

-- | OCaml's 128-bit Hex64 vector → BigInt. Handles two yojson shapes:
-- |   * `{"inner": [int64, int64]}` (`Scalar_challenge.t`)
-- |   * `[int64, int64]` (raw `Limb_vector.Constant.t Vector_2.t`)
decodeChallengeBI :: Json -> Either JsonDecodeError BigInt
decodeChallengeBI j =
  case decodeJson j :: Either JsonDecodeError (Array Json) of
    Right arr -> traverse decodeInt64 arr <#> combineLimbsLE
    Left _ -> do
      obj <- decodeJson j
      innerJ <- obj .: "inner"
      decodeLimbVec innerJ

-- | Wrap a decoded 128-bit BigInt as `SizedF 128 (F StepField)`.
mkScalarChallenge :: BigInt -> SizedF 128 (F StepField)
mkScalarChallenge bi =
  let
    f = fromBigInt bi :: StepField
    -- 128-bit value is guaranteed to fit in our 255-bit field, so the
    -- Partial constraint on `unsafeFromField` is safely discharged.
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

-- | WrapField variants of the challenge decoders, for the 15-round
-- | `messages_for_next_wrap_proof.old_bulletproof_challenges` (the prev
-- | proof's WRAP IPA challenges, used in the wrap-message digest). Same
-- | wire shape as the step ones, just the other field.
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

-- | Decode `proof_state.sponge_digest_before_evaluations` which is a
-- | `Digest.Constant.t = Hex64 vector of 4 limbs` = 256-bit value.
decodeDigestField :: Json -> Either JsonDecodeError StepField
decodeDigestField j = do
  bi <- decodeLimbVec j
  pure (fromBigInt bi)

-- | Decode `branch_data` and project out `domain_log2 :: Int`.
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

-- | OCaml polymorphic-variant `N0 | N1 | N2` is yojson-encoded as a single-
-- | element array `["N0"]` etc. Map to the PS `Vector 2 Boolean` mask.
-- |
-- | This is the CONSTANT branch_data packing, which OCaml's `Branch_data.pack`
-- | (`branch_data.ml:62-73`) does via `project (Proofs_verified.to_bool_vec …)`
-- | — NOT the prefix-mask used by the in-circuit `proofs_verified_mask`. Per
-- | `pickles_base/proofs_verified.ml:70-76` `to_bool_vec` is:
-- |   N0 → [false, false], N1 → [false, true], N2 → [true, true].
-- | LSB-first `project` then gives N0→0, N1→2, N2→3 — matching the wrap
-- | public input. (`packBranchDataWrap` packs `m0 + 2·m1`, and the in-circuit
-- | path reaches the same values via `revOnesVector`, which also produces the
-- | `to_bool_vec` shape — so this decode must use `to_bool_vec`, not the
-- | prefix mask. N0/N2 coincide between the two conventions; only N1 differs.)
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

-- | OCaml `Limb_vector.Constant.Hex64.t` for a single byte (= `domain_log2`)
-- | is yojson-encoded as a 1-character string. Char code is the byte value.
decodeOcamlByte :: Json -> Either JsonDecodeError Int
decodeOcamlByte j = do
  s <- decodeJson j :: Either JsonDecodeError String
  case charAt 0 s of
    Just c -> pure (toCharCode c)
    Nothing -> Left (TypeMismatch ("expected single-char byte string, got empty"))

--------------------------------------------------------------------------------
-- AllEvals decoder
--------------------------------------------------------------------------------

-- | Decode `prev_evals :: Plonk_types.All_evals.t` from
-- | `proof.json/prev_evals`. See the original NRR fixture for the JSON shape:
-- | a flat `[zeta, omega_zeta]` `public_input` plus the kimchi
-- | `proof_evaluations` (chunked-singleton) for the 6 always-on selectors,
-- | `z`, `w` (15), `coefficients` (15) and `s` (6).
decodeAllEvals :: Json -> Either JsonDecodeError (ChunkedAllEvals StepField)
decodeAllEvals j = do
  obj <- decodeJson j
  ftJ <- obj .: "ft_eval1"
  ftEval1 <- decodeHex ftJ :: Either JsonDecodeError StepField

  evalsObj <- (obj .: "evals") >>= decodeJson
  publicJ <- evalsObj .: "public_input"
  -- Public input in OCaml's prev_evals dump is flat `[zeta, omega]` — a
  -- length-1 chunk. Wrap as a singleton NEA to fit the ChunkedAllEvals
  -- shape.
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

-- | Decode a flat-format point eval: `[zeta_hex, omega_zeta_hex]`.
-- | Used for `prev_evals.evals.public_input`.
decodePointEvalFlat :: Json -> Either JsonDecodeError (PointEval StepField)
decodePointEvalFlat j = do
  arr <- decodeJson j :: Either JsonDecodeError (Array Json)
  case arr of
    [ zetaJ, omegaJ ] -> do
      zeta <- decodeHex zetaJ
      omegaTimesZeta <- decodeHex omegaJ
      pure { zeta, omegaTimesZeta }
    _ -> Left (TypeMismatch ("decodePointEvalFlat: expected 2-elem array"))

-- | Decode a chunked point eval: `[[zeta_hex...], [omega_zeta_hex...]]`.
-- | Used for the kimchi `proof_evaluations` inside `prev_evals.evals.evals`.
-- | At num_chunks=N each inner array has length N; both arrays must
-- | agree on N. Returns one `PointEval` per chunk index.
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
          -- Pair element-wise; safe because lengths match (checked above).
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
