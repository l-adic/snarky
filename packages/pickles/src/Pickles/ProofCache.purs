-- | Disk proof-cache — a faithful translation of OCaml
-- | `mina/src/lib/crypto/pickles/proof_cache.ml`.
-- |
-- | A 2-level map `verification_key -> public_input -> proof`, where the
-- | proof is the kimchi `ProverProof` serde-JSON (exactly OCaml's
-- | `Backend.Tick/Tock.Proof.{to,of}_yojson`). Step and wrap proofs are
-- | cached separately, each keyed by *its own* circuit's VK digest and
-- | *its own* kimchi public-input field vector.
-- |
-- | Why `(vk, public_input)` is a complete key: the kimchi prover is
-- | deterministic (shared ChaCha20 seed) and, for pickles circuits, the
-- | recursion-relevant non-deterministic advice is hash-committed into
-- | the step statement (= the public input); remaining advice is
-- | constraint-determined. So the public input pins the proof — no
-- | label, no prev-traversal. This is the property OCaml's `Proof_cache`
-- | itself relies on (and mina ships, with committed `proof_cache.json`
-- | per transaction_snark test).
-- |
-- | Storage is one JSON document per test, read/written through the
-- | PureScript `node-fs` bindings; the store is the well-typed
-- | `Object (Object String)` (= `vk -> public_input -> proof`). Decode
-- | is graceful (any drift => empty store => miss => regenerate), per
-- | `proof_cache.ml`.
module Pickles.ProofCache
  ( ProofCache
  , mkProofCache
  , getStepProof
  , setStepProof
  , getWrapProof
  , setWrapProof
  , vestaVerifierIndexJsonKey
  ) where

import Prelude

import Data.Argonaut.Core (Json, stringify)
import Data.Argonaut.Core (fromArray, fromNumber, fromObject, fromString, jsonNull) as Argonaut
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Data.String (Pattern(..), lastIndexOf, take)
import Data.String.Common (joinWith)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Foreign.Object (Object)
import Foreign.Object as Object
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (exists, mkdir', readTextFile, writeTextFile)
import Pickles.Field (StepField, WrapField)
import Pickles.Prove.FFI (Proof)
import Pickles.Sideload.FFI (pallasProofFromSerdeJson, pallasProofToSerdeJson, vestaProofFromSerdeJson, vestaProofToSerdeJson)
import Simple.JSON as JSON
import Snarky.Backend.Kimchi.Types (VerifierIndex)
import Snarky.Curves.Class (class PrimeField, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta

-- | Handle to a per-test cache file. The on-disk document is the source
-- | of truth (mirrors OCaml's `ref`); each `get`/`set` reads it fresh
-- | so a populating run accumulates correctly and a later run sees
-- | every entry.
newtype ProofCache = ProofCache String

mkProofCache :: String -> ProofCache
mkProofCache = ProofCache

-- | On-disk shape: `{ "<vkKey>": { "<publicInputKey>": "<proofSerdeJson>" } }`
-- | — the natural JSON form of OCaml's `vk -> public_input -> proof`.
type Store = Object (Object String)

-- | Load the store. Missing file or any decode drift => empty store
-- | (a miss); the proof is simply regenerated. A cache must always be
-- | reconstructible from empty (same invariant as `proof_cache.ml`).
loadStore :: String -> Effect Store
loadStore path = do
  present <- exists path
  if not present then pure Object.empty
  else do
    txt <- readTextFile UTF8 path
    pure (fromMaybe Object.empty (JSON.readJSON_ txt :: Maybe Store))

-- | Write the store through, creating the containing directory if
-- | needed (recursive mkdir is idempotent — no throw if it exists).
saveStore :: String -> Store -> Effect Unit
saveStore path store = do
  case lastIndexOf (Pattern "/") path of
    Just i -> mkdir' (take i path) { recursive: true, mode: permsAll }
    Nothing -> pure unit
  writeTextFile UTF8 path (JSON.writeJSON store)

getStr :: ProofCache -> String -> String -> Effect (Maybe String)
getStr (ProofCache path) vk pi = do
  store <- loadStore path
  pure (Object.lookup vk store >>= Object.lookup pi)

setStr :: ProofCache -> String -> String -> String -> Effect Unit
setStr (ProofCache path) vk pi val = do
  store <- loadStore path
  let inner = fromMaybe Object.empty (Object.lookup vk store)
  saveStore path (Object.insert vk (Object.insert pi val inner) store)

-- | Canonical, deterministic string for a field element (its integer
-- | value). Stable across runs/machines.
fieldStr :: forall f. PrimeField f => f -> String
fieldStr = show <<< toBigInt

-- | Public-input field vector → its canonical key (OCaml keys by
-- | `[%to_yojson: Field.t array]`; same content, our string form).
piKey :: forall f. PrimeField f => Array f -> String
piKey = joinWith "," <<< map fieldStr

-- | Step / wrap VK lookup key. Mirrors OCaml `Proof_cache` semantics
-- | (`proof_cache.ml:185`): the full VK JSON serves as the bucket key
-- | rather than a digest. OCaml never materializes a host-side VK digest;
-- | we follow suit instead of porting kimchi's `PlonkSpongeConstantsKimchi`
-- | sponge to JS.
stepVkKey :: VerifierIndex Vesta.G Pallas.BaseField -> String
stepVkKey vk = "step:" <> pallasVerifierIndexJsonKey vk

wrapVkKey :: VerifierIndex Pallas.G Vesta.BaseField -> String
wrapVkKey vk = "wrap:" <> vestaVerifierIndexJsonKey vk

-- | Step proof lookup / store (= OCaml `get/set_step_proof`).
getStepProof
  :: ProofCache
  -> VerifierIndex Vesta.G Pallas.BaseField
  -> Array StepField
  -> Effect (Maybe (Proof Vesta.G Pallas.BaseField))
getStepProof cache vk pis = do
  m <- getStr cache (stepVkKey vk) (piKey pis)
  pure (pallasProofFromSerdeJson <$> m)

setStepProof
  :: ProofCache
  -> VerifierIndex Vesta.G Pallas.BaseField
  -> Array StepField
  -> Proof Vesta.G Pallas.BaseField
  -> Effect Unit
setStepProof cache vk pis proof =
  setStr cache (stepVkKey vk) (piKey pis) (pallasProofToSerdeJson proof)

-- | Wrap proof lookup / store (= OCaml `get/set_wrap_proof`).
getWrapProof
  :: ProofCache
  -> VerifierIndex Pallas.G Vesta.BaseField
  -> Array WrapField
  -> Effect (Maybe (Proof Pallas.G Vesta.BaseField))
getWrapProof cache vk pis = do
  m <- getStr cache (wrapVkKey vk) (piKey pis)
  pure (vestaProofFromSerdeJson <$> m)

setWrapProof
  :: ProofCache
  -> VerifierIndex Pallas.G Vesta.BaseField
  -> Array WrapField
  -> Proof Pallas.G Vesta.BaseField
  -> Effect Unit
setWrapProof cache vk pis proof =
  setStr cache (wrapVkKey vk) (piKey pis) (vestaProofToSerdeJson proof)

--------------------------------------------------------------------------------
-- VK json-key: the deterministic full-VK string used as the bucket key.
--
-- Mirrors OCaml `Pickles.Proof_cache`'s keying (`proof_cache.ml:185`): the
-- cache is `verifier_key_yojson -> public_input_yojson -> proof`, so two VKs
-- share a bucket iff they serialize identically. OCaml never materializes a
-- host-side VK digest, so neither do we — the full VK JSON *is* the key.
--
-- The JS side (`_vkRaw`) does exactly two irreducible things: reach into the
-- napi `VerifierIndex`'s snake_case fields, and hex-encode the 32-byte
-- buffers. All JSON-shape policy lives here in PS via Argonaut. The fields
-- match OCaml's `[%to_yojson: verifier_index]` (`proof_cache.ml:152-163`):
-- domain, max_poly_size, public, prev_challenges, evals, shifts, zk_rows
-- (`srs` is rendered `null` by OCaml and the optional `lookup_index` is
-- `None` for vanilla pickles VKs, so both are skipped).
--
-- Only `vestaVerifierIndexJsonKey` is exported (the digest-equality test
-- consumes it); `pallasVerifierIndexJsonKey` + the `VkRaw`/helper types
-- stay private to this module.
--------------------------------------------------------------------------------

pallasVerifierIndexJsonKey :: VerifierIndex Vesta.G Pallas.BaseField -> String
pallasVerifierIndexJsonKey = stringify <<< vkRawToJson <<< _vkRaw

vestaVerifierIndexJsonKey :: VerifierIndex Pallas.G Vesta.BaseField -> String
vestaVerifierIndexJsonKey = stringify <<< vkRawToJson <<< _vkRaw

-- | Raw decomposition of a kimchi `VerifierIndex` napi-object into PS.
-- | Bytes come pre-hex-encoded from JS. Optional gate-commitments are
-- | `Nullable` (napi-rs renders `Option<X>` as `X | null | undefined`;
-- | `Nullable.toMaybe` collapses both to `Nothing`).
type VkPolyCommRaw = { unshifted :: Array { x :: String, y :: String } }

type VkEvalsRaw =
  { sigmaComm :: Array VkPolyCommRaw
  , coefficientsComm :: Array VkPolyCommRaw
  , genericComm :: VkPolyCommRaw
  , psmComm :: VkPolyCommRaw
  , completeAddComm :: VkPolyCommRaw
  , mulComm :: VkPolyCommRaw
  , emulComm :: VkPolyCommRaw
  , endomulScalarComm :: VkPolyCommRaw
  , xorComm :: Nullable VkPolyCommRaw
  , rangeCheck0Comm :: Nullable VkPolyCommRaw
  , rangeCheck1Comm :: Nullable VkPolyCommRaw
  , foreignFieldAddComm :: Nullable VkPolyCommRaw
  , foreignFieldMulComm :: Nullable VkPolyCommRaw
  , rotComm :: Nullable VkPolyCommRaw
  }

type VkRaw =
  { domain :: { logSizeOfGroup :: Int, groupGen :: String }
  , maxPolySize :: Int
  , publicInputs :: Int
  , prevChallenges :: Int
  , zkRows :: Int
  , shifts :: Array String -- 7 elements (s0..s6), each hex-encoded
  , evals :: VkEvalsRaw
  }

foreign import _vkRaw :: forall g f. VerifierIndex g f -> VkRaw

affineToJson :: { x :: String, y :: String } -> Json
affineToJson p = Argonaut.fromArray [ Argonaut.fromString p.x, Argonaut.fromString p.y ]

polyCommToJson :: VkPolyCommRaw -> Json
polyCommToJson pc = Argonaut.fromArray (map affineToJson pc.unshifted)

maybePolyCommToJson :: Nullable VkPolyCommRaw -> Json
maybePolyCommToJson n = case Nullable.toMaybe n of
  Nothing -> Argonaut.jsonNull
  Just pc -> polyCommToJson pc

-- Insertion-ordered field list — `Foreign.Object` preserves insertion
-- order, matching V8 `JSON.stringify(...)` so the key stays stable.
obj :: Array (Tuple String Json) -> Json
obj = Argonaut.fromObject <<< Object.fromFoldable

evalsToJson :: VkEvalsRaw -> Json
evalsToJson e = obj
  [ Tuple "sigmaComm" (Argonaut.fromArray (map polyCommToJson e.sigmaComm))
  , Tuple "coefficientsComm" (Argonaut.fromArray (map polyCommToJson e.coefficientsComm))
  , Tuple "genericComm" (polyCommToJson e.genericComm)
  , Tuple "psmComm" (polyCommToJson e.psmComm)
  , Tuple "completeAddComm" (polyCommToJson e.completeAddComm)
  , Tuple "mulComm" (polyCommToJson e.mulComm)
  , Tuple "emulComm" (polyCommToJson e.emulComm)
  , Tuple "endomulScalarComm" (polyCommToJson e.endomulScalarComm)
  , Tuple "xorComm" (maybePolyCommToJson e.xorComm)
  , Tuple "rangeCheck0Comm" (maybePolyCommToJson e.rangeCheck0Comm)
  , Tuple "rangeCheck1Comm" (maybePolyCommToJson e.rangeCheck1Comm)
  , Tuple "foreignFieldAddComm" (maybePolyCommToJson e.foreignFieldAddComm)
  , Tuple "foreignFieldMulComm" (maybePolyCommToJson e.foreignFieldMulComm)
  , Tuple "rotComm" (maybePolyCommToJson e.rotComm)
  ]

vkRawToJson :: VkRaw -> Json
vkRawToJson r = obj
  [ Tuple "domain"
      ( obj
          [ Tuple "logSizeOfGroup" (Argonaut.fromNumber (toNumber r.domain.logSizeOfGroup))
          , Tuple "groupGen" (Argonaut.fromString r.domain.groupGen)
          ]
      )
  , Tuple "maxPolySize" (Argonaut.fromNumber (toNumber r.maxPolySize))
  , Tuple "public" (Argonaut.fromNumber (toNumber r.publicInputs))
  , Tuple "prevChallenges" (Argonaut.fromNumber (toNumber r.prevChallenges))
  , Tuple "evals" (evalsToJson r.evals)
  , Tuple "shifts" (Argonaut.fromArray (map Argonaut.fromString r.shifts))
  , Tuple "zkRows" (Argonaut.fromNumber (toNumber r.zkRows))
  ]
