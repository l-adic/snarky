-- | Test-only loader for OCaml-emitted Pickles side-load fixtures.
-- |
-- | Reads three files written by an OCaml-side `dump_*_fixtures.exe` tool
-- | (see `mina/src/lib/crypto/pickles/dump_nrr_fixtures/` for the NRR
-- | example):
-- |   * `vk.serde.json`   — kimchi `VerifierIndex` Rust serde JSON
-- |   * `proof.json`      — full Pickles `Proof.t` via OCaml `to_yojson_full`
-- |   * `statement.json`  — the application's public input/output
-- |
-- | Returns a `LoadedFixture stmtVal` containing:
-- |   * Opaque VK + wire proof FFI handles
-- |   * Native PS records for the Pickles wrapping (rawPlonk,
-- |     rawBulletproofChallenges, branchData, spongeDigest,
-- |     challengePolynomialCommitment, stepDomainLog2)
-- |   * AllEvals (= prev_evals) and pEval0Chunks
-- |   * The application statement, decoded by a caller-supplied function
-- |
-- | The `stmtVal` parameter generalises across applications: NRR's
-- | statement is a single `StepField`; richer apps (Simple_chain,
-- | Two_phase_chain, Tree_proof_return) supply their own decoder.
-- |
-- | OCaml-yojson encodes 128-bit `Hex64` values as JSON int64 pairs that
-- | exceed JS Number precision (2^53). We use `json-bigint` via
-- | `parseJsonPreserveBigInts` to re-emit int64s as JSON strings before
-- | argonaut decoding.
module Test.Pickles.Sideload.Loader
  ( LoadedFixture
  , loadFixture
  , loadNrrFixture
  , fromHexBe
  , parseJsonPreserveBigInts
  , wrapSrsDepthLog2
  ) where

import Prelude

import Data.Argonaut.Core (Json)
import Data.Argonaut.Decode (JsonDecodeError(..), decodeJson, printJsonDecodeError, (.:))
import Data.Argonaut.Parser (jsonParser)
import Data.Array as Array
import Data.Bifunctor (lmap)
import Data.Char (toCharCode)
import Data.Either (Either(..), either)
import Data.Maybe (Maybe(..))
import Data.String.CodeUnits (charAt)
import Data.Traversable (traverse)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Type.Proxy (Proxy(..))
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
import Pickles.Dummy (baseCaseDummies, computeDummySgValues, dummyIpaChallenges)
import Pickles.Linearization.FFI (PointEval)
import Pickles.PlonkChecks (AllEvals)
import Pickles.ProofFFI (Proof)
import Pickles.Prove.Step (extractWrapVKForStepHash)
import Pickles.Prove.Verify
  ( SomeCompiledProofWidthData
  , mkSomeCompiledProofWidthData
  )
import Pickles.Sideload.FFI (noOptionalFeatures, vestaHydrateVerifierIndex, vestaProofFromSerdeJson, vestaVerifierIndexFromSerdeJson)
import Pickles.Step.MessageHash (hashMessagesForNextStepProofPure)
import Pickles.Types (PaddedLength, StepField, StepIPARounds, WrapField)
import Pickles.Verify.Types (BranchData, PlonkMinimal, ScalarChallenge)
import Pickles.Wrap.MessageHash (hashMessagesForNextWrapProofPureGeneral)
import Snarky.Backend.Kimchi.Class (createCRS)
import Unsafe.Coerce (unsafeCoerce)
import Snarky.Backend.Kimchi.Impl.Pallas (pallasCrsCreate)
import Snarky.Backend.Kimchi.Types (CRS, VerifierIndex)
import Snarky.Circuit.DSL (F)
import Snarky.Circuit.DSL.SizedF (SizedF, unsafeFromField, wrapF)
import Snarky.Curves.Class (class PrimeField, fromBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)

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

-- | The wrap-side SRS depth (matching OCaml's `Backend.Tock.Rounds.n` = 15).
wrapSrsDepthLog2 :: Int
wrapSrsDepthLog2 = 15

--------------------------------------------------------------------------------
-- Fixture surface
--------------------------------------------------------------------------------

type LoadedFixture stmtVal =
  { vk :: VerifierIndex Pallas.G WrapField
  , vkJson :: String
  , vestaSrs :: CRS Vesta.G
  , wireProof :: Proof Pallas.G Vesta.BaseField
  , statement :: stmtVal

  -- Decoded Pickles wrapping
  , rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField
  , challengePolynomialCommitment :: AffinePoint WrapField
  , stepDomainLog2 :: Int

  -- prev_evals (the inner step proof's polynomial evaluations)
  , prevEvals :: AllEvals StepField
  , pEval0Chunks :: Array StepField

  -- Phase 5.2: message digests (computed for max_proofs_verified = 0).
  , messagesForNextStepProofDigest :: StepField
  , messagesForNextWrapProofDigest :: WrapField

  -- Phase 5.3: width-existential carrier of width-indexed prev-proof data.
  -- For NRR (mpv = 0) the inner Vector width fields are all empty;
  -- `verifyOne` reads only `oldBulletproofChallenges`, which is
  -- `Vector.nil`. Other CompiledProofWidthData fields (wrapDvInput
  -- specifically) are present for type-fit but unread by the verify
  -- path.
  , widthData :: SomeCompiledProofWidthData
  }

-- | Generic fixture loader. Caller supplies:
-- |   * `decode`: parse the application's statement JSON
-- |   * `toFields`: flatten the statement value to field elements (used by
-- |     `hashMessagesForNextStepProofPure` to build the
-- |     `messagesForNextStepProofDigest`).
-- |
-- | Currently specialised for max_proofs_verified = 0 (NRR-shape): the
-- | message digests are computed assuming there are no previous proofs.
-- | Generalising to mpv > 0 would thread real prev-proof data through
-- | the digest computation here.
loadFixture
  :: forall stmtVal
   . { decode :: Json -> Either JsonDecodeError stmtVal
     , toFields :: stmtVal -> Array StepField
     }
  -> String
  -> Aff (LoadedFixture stmtVal)
loadFixture cfg dir = do
  vkJson <- liftEffect $ readTextFile UTF8 (dir <> "/vk.serde.json")
  proofSerdeJson <- liftEffect $ readTextFile UTF8 (dir <> "/proof.serde.json")
  wrappingText <- liftEffect $ readTextFile UTF8 (dir <> "/wrapping.json")
  statementText <- liftEffect $ readTextFile UTF8 (dir <> "/statement.json")

  let
    -- Re-encode int64s as JSON strings so argonaut doesn't lose precision.
    wrappingTextSafe = parseJsonPreserveBigInts wrappingText

    srs = pallasCrsCreate (1 `shl` wrapSrsDepthLog2)
    -- Deserialize → hydrate. The serde codec leaves `linearization` and
    -- `powers_of_alpha` empty (`#[serde(skip)]`); without re-attaching
    -- them, kimchi's verify panics with "constraint Permutation was not
    -- registered". Pickles wrap circuits enable no optional gates and
    -- always have the Generic gate, so `noOptionalFeatures` + `generic
    -- = true` is the right pair for any Pickles-produced wrap VK.
    dehydratedVk = vestaVerifierIndexFromSerdeJson vkJson srs
    vk = vestaHydrateVerifierIndex dehydratedVk noOptionalFeatures true

    -- Kimchi proof: load via the same Rust serde codec OCaml wrote it
    -- with. `prev_challenges` is already populated (OCaml passed the
    -- `Wrap_hack.pad_accumulator` chal_polys at dump time), so we
    -- never reconstruct it on the PS side.
    wireProof = vestaProofFromSerdeJson proofSerdeJson

  statement <- liftEffectThrow $ parseStatement cfg.decode statementText
  decoded <- liftEffectThrow $ decodePickles wrappingTextSafe

  -- Vesta SRS for `mkSomeCompiledProofWidthData`'s `dummyChalPolyComm`
  -- filler — verifier internals don't read it for NRR (mpv = 0) but
  -- the existential needs *some* value at construction time.
  vestaSrs <- liftEffect $ createCRS @StepField

  let
    appStateFields = cfg.toFields statement
    bcd = baseCaseDummies { maxProofsVerified: 0 }
    dummySgs = computeDummySgValues bcd srs vestaSrs
    dummyWrapSgInStepField = dummySgs.ipa.wrap.sg

    -- Phase 5.3: empty width-indexed widthData for mpv = 0.
    --
    -- `wrapDvInput` is only consulted by prover-side machinery; verifyOne
    -- doesn't read it. Filling with `unsafeCoerce {}` keeps the type-fit
    -- without us having to fabricate an inner step proof + step VK from
    -- the loaded fixture (which only carries the *wrap* side).
    widthData :: SomeCompiledProofWidthData
    widthData = mkSomeCompiledProofWidthData @0 @PaddedLength
      { oldBulletproofChallenges: Vector.nil
      , msgWrapChallenges: Vector.nil
      , outerStepChalPolyComms: Vector.nil
      , wrapDvInput: unsafeCoerce {}
      , dummyOldBp: dummyIpaChallenges.stepExpanded
      , dummyMsgWrap: dummyIpaChallenges.wrapExpanded
      , dummyChalPolyComm: dummyWrapSgInStepField
      }

    -- For mpv = 0: no previous proofs, so the proofs vector is empty.
    -- Mirrors `extractWrapVKForStepHash input.wrapVK` from
    -- `Pickles.Prove.Step:701`. The real prev (sg, expandedBpChals) entries
    -- would go here for mpv > 0.
    wrapVkStep = extractWrapVKForStepHash vk
    msgStep :: StepField
    msgStep = hashMessagesForNextStepProofPure
      { stepVk: wrapVkStep
      , appState: appStateFields
      , proofs: Vector.nil :: Vector 0 _
      }

    -- For mpv = 0: paddedChallenges = full Vector PaddedLength of dummy
    -- expanded wrap-IPA challenges. Mirrors `msgWrapPadded` construction
    -- in `Pickles.Prove.Compile:2830-2833` with `padMax = PaddedLength`.
    msgWrapPadded :: Vector PaddedLength (Vector _ WrapField)
    msgWrapPadded = Vector.replicate @PaddedLength dummyIpaChallenges.wrapExpanded

    msgWrap :: WrapField
    msgWrap = hashMessagesForNextWrapProofPureGeneral
      { sg: decoded.challengePolynomialCommitment
      , paddedChallenges: msgWrapPadded
      }

  pure
    { vk
    , vkJson
    , vestaSrs
    , wireProof
    , statement
    , rawPlonk: decoded.rawPlonk
    , rawBulletproofChallenges: decoded.rawBulletproofChallenges
    , branchData: decoded.branchData
    , spongeDigestBeforeEvaluations: decoded.spongeDigestBeforeEvaluations
    , challengePolynomialCommitment: decoded.challengePolynomialCommitment
    , stepDomainLog2: decoded.stepDomainLog2
    , prevEvals: decoded.prevEvals
    , pEval0Chunks: decoded.pEval0Chunks
    , messagesForNextStepProofDigest: msgStep
    , messagesForNextWrapProofDigest: msgWrap
    , widthData
    }

-- | NRR convenience: NRR's `Output Field.typ` makes the statement a single
-- | hex-encoded `StepField`. `toFields` wraps it in a singleton array — the
-- | shape `hashMessagesForNextStepProofPure` expects for `appState`.
loadNrrFixture :: String -> Aff (LoadedFixture StepField)
loadNrrFixture = loadFixture
  { decode: decodeHex
  , toFields: \x -> [ x ]
  }

shl :: Int -> Int -> Int
shl x n = x * pow2 n
  where
  pow2 :: Int -> Int
  pow2 0 = 1
  pow2 k = 2 * pow2 (k - 1)

liftEffectThrow :: forall a. Either String a -> Aff a
liftEffectThrow = either (\msg -> liftEffect (throw msg)) pure

--------------------------------------------------------------------------------
-- Hex / int64 / BigInt helpers
--------------------------------------------------------------------------------

-- | Parse a big-endian hex string (e.g. `"0x2B7F..."`) into a prime-field
-- | element. OCaml's `Pasta_field.to_yojson` emits BE hex with `0x` prefix.
fromHexBe :: forall f. PrimeField f => String -> f
fromHexBe s = case JsBigInt.fromString s of
  Just bi -> fromBigInt bi
  Nothing -> unsafeCrashWith ("fromHexBe: failed to parse " <> s)

decodeHex :: forall f. PrimeField f => Json -> Either JsonDecodeError f
decodeHex j = do
  s <- decodeJson j :: Either JsonDecodeError String
  pure (fromHexBe s)

decodeAffinePoint :: forall f. PrimeField f => Json -> Either JsonDecodeError (AffinePoint f)
decodeAffinePoint j = do
  arr <- decodeJson j :: Either JsonDecodeError (Array Json)
  case arr of
    [ x, y ] -> do
      x' <- decodeHex x
      y' <- decodeHex y
      pure { x: x', y: y' }
    _ -> Left (TypeMismatch ("expected 2-element [x, y] curve point, got " <> show (Array.length arr) <> " elements"))

-- | Decode a JSON int64. After `parseJsonPreserveBigInts` rewrites
-- | numbers above ±2^53 as strings, smaller integers stay as JSON
-- | numbers. We try three forms in order:
-- |   * `String` — produced by `parseJsonPreserveBigInts` for ints
-- |     above ±2^53 (and for OCaml-string-encoded fields).
-- |   * `Number` — JSON numbers in the safe-integer range. Covers
-- |     ints up to ±2^53; PureScript `Int` only covers ±2^31, so we
-- |     can't decode as Int directly without losing medium-sized
-- |     values (e.g. OCaml `802613802914978`).
-- |   * `Int` — final fallback for the narrow ±2^31 case (kept for
-- |     backwards compatibility; `Number` covers a strict superset).
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
    twoTo64 :: BigInt
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
-- Phase 5.0: Pickles wrapping decoders
--------------------------------------------------------------------------------

type DecodedPickles =
  { rawPlonk :: PlonkMinimal (F StepField)
  , rawBulletproofChallenges :: Vector StepIPARounds (ScalarChallenge (F StepField))
  , branchData :: BranchData StepField Boolean
  , spongeDigestBeforeEvaluations :: StepField
  , challengePolynomialCommitment :: AffinePoint WrapField
  , stepDomainLog2 :: Int
  , prevEvals :: AllEvals StepField
  , pEval0Chunks :: Array StepField
  }

decodePickles :: String -> Either String DecodedPickles
decodePickles raw = do
  json <- jsonParser raw
  lmap printJsonDecodeError (decodePicklesJson json)

decodePicklesJson :: Json -> Either JsonDecodeError DecodedPickles
decodePicklesJson j = do
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

  -- Phase 5.1: prev_evals
  prevEvalsJ <- (obj .: "prev_evals") >>= decodeJson
  prevEvals <- decodeAllEvals prevEvalsJ
  let pEval0Chunks = [ prevEvals.publicEvals.zeta ]

  pure
    { rawPlonk
    , rawBulletproofChallenges: bpVec
    , branchData
    , spongeDigestBeforeEvaluations: sponge
    , challengePolynomialCommitment: cpc
    , stepDomainLog2
    , prevEvals
    , pEval0Chunks
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
-- | element array `["N0"]` etc. Map to the PS `Vector 2 Boolean` mask using
-- | the prefix-mask convention from `pickles_base/proofs_verified.ml:24-28`:
-- |   N0 → [false, false], N1 → [true, false], N2 → [true, true].
decodeProofsVerified :: Json -> Either JsonDecodeError (Vector 2 Boolean)
decodeProofsVerified j = do
  arr :: Array Json <- decodeJson j
  case arr of
    [ tagJ ] -> do
      tag <- decodeJson tagJ :: Either JsonDecodeError String
      case tag of
        "N0" -> pure (mkMask false false)
        "N1" -> pure (mkMask true false)
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
-- Phase 5.1: AllEvals decoder
--------------------------------------------------------------------------------

-- | Decode `prev_evals :: Plonk_types.All_evals.t` from
-- | `proof.json/prev_evals`.
-- |
-- | The JSON shape is:
-- |   { "ft_eval1": "0x..."
-- |   , "evals":
-- |       { "public_input": [zeta_hex, omega_zeta_hex]   -- flat point eval
-- |       , "evals":   -- kimchi proof_evaluations, chunked-singleton format
-- |           { "w": [[[zeta_hex],[omega_zeta_hex]], × 15]
-- |           , "coefficients": [[[..],[..]], × 15]
-- |           , "z": [[zeta],[omega_zeta]]
-- |           , "s": [[[..],[..]], × 6]
-- |           , "generic_selector": [[..],[..]]
-- |           , "poseidon_selector": [[..],[..]]
-- |           , "complete_add_selector": [[..],[..]]
-- |           , "mul_selector": [[..],[..]]
-- |           , "emul_selector": [[..],[..]]
-- |           , "endomul_scalar_selector": [[..],[..]]
-- |           , "range_check{0,1}_selector": null
-- |           , ... 16 optional selectors all null for Features.none
-- |           } } }
-- |
-- | We read the 6 always-on selectors as the `indexEvals` vector in the
-- | OCaml absorption order (`generic`, `poseidon`, `complete_add`, `mul`,
-- | `emul`, `endomul_scalar` — matching `extractEvalFields` in
-- | `Pickles.PlonkChecks`).
decodeAllEvals :: Json -> Either JsonDecodeError (AllEvals StepField)
decodeAllEvals j = do
  obj <- decodeJson j
  ftJ <- obj .: "ft_eval1"
  ftEval1 <- decodeHex ftJ :: Either JsonDecodeError StepField

  evalsObj <- (obj .: "evals") >>= decodeJson
  publicJ <- evalsObj .: "public_input"
  publicEvals <- decodePointEvalFlat publicJ

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

-- | Decode a chunked-singleton point eval: `[[zeta_hex], [omega_zeta_hex]]`.
-- | Used for the kimchi `proof_evaluations` inside `prev_evals.evals.evals`.
-- | For num_chunks=1, each chunk array has length 1.
decodePointEvalChunked :: Json -> Either JsonDecodeError (PointEval StepField)
decodePointEvalChunked j = do
  arr <- decodeJson j :: Either JsonDecodeError (Array Json)
  case arr of
    [ zetaArrJ, omegaArrJ ] -> do
      zetaArr :: Array Json <- decodeJson zetaArrJ
      omegaArr :: Array Json <- decodeJson omegaArrJ
      case zetaArr, omegaArr of
        [ zJ ], [ oJ ] -> do
          zeta <- decodeHex zJ
          omegaTimesZeta <- decodeHex oJ
          pure { zeta, omegaTimesZeta }
        _, _ -> Left
          ( TypeMismatch
              ( "decodePointEvalChunked: expected singleton chunks, got "
                  <> show (Array.length zetaArr)
                  <> "/"
                  <> show (Array.length omegaArr)
              )
          )
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

