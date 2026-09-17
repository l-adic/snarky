-- | Disk proof-cache: the prover's memo of every kimchi proof a test has
-- | produced, and the record a consumer verifies those proofs from.
-- |
-- | A 2-level map `vkDigest -> publicInput -> Entry`. The digest is
-- | `VerifierIndex::digest()`, the value the verifier absorbs first; the
-- | public input is the comma-joined decimal field vector. An entry holds
-- | the verification key's JSON, the proof's serde-JSON (exactly OCaml's
-- | `Backend.Tick/Tock.Proof.{to,of}_yojson`) and the keys of the proofs
-- | it is built on — a wrap proof's the step proof it wrapped, a step
-- | proof's the wrap proofs it verified — so a chain is walkable from
-- | the file alone.
-- |
-- | Why `(vkDigest, publicInput)` is a complete key: the kimchi prover is
-- | deterministic (shared ChaCha20 seed) and, for pickles circuits, the
-- | recursion-relevant non-deterministic advice is hash-committed into
-- | the step statement (= the public input); remaining advice is
-- | constraint-determined. So the public input pins the proof — no
-- | label, no prev-traversal.
-- |
-- | Storage is one JSON document per test, read/written through the
-- | PureScript `node-fs` bindings. Decode is graceful: any drift is an
-- | empty store, a miss, and the proof regenerates.
module Snarky.Backend.Kimchi.ProofCache
  ( ProofCache
  , mkProofCache
  , Entry
  , Links(..)
  , ProofRef
  , getPallasProof
  , setPallasProof
  , getVestaProof
  , setVestaProof
  , piKey
  , pallasVerifierIndexJsonKey
  , vestaVerifierIndexJsonKey
  ) where

import Prelude

import Data.Argonaut.Core (Json, stringify)
import Data.Argonaut.Core (fromArray, fromNumber, fromObject, fromString, jsonNull) as Argonaut
import Data.Array (mapMaybe)
import Data.Int (toNumber)
import Data.Maybe (Maybe(..), fromMaybe, isJust)
import Data.Nullable (Nullable)
import Data.Nullable as Nullable
import Data.String (Pattern(..), lastIndexOf, take)
import Data.String.Common (joinWith)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Foreign.Object (Object)
import Foreign.Object as Object
import JS.BigInt as BigInt
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (exists, mkdir', readTextFile, writeTextFile)
import Simple.JSON as JSON
import Snarky.Backend.Kimchi.Proof (Proof, pallasProofFromSerdeJson, pallasProofToSerdeJson, vestaProofFromSerdeJson, vestaProofToSerdeJson)
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

-- | The cache key of another entry.
type ProofRef = { vkDigest :: String, publicInput :: String }

-- | What a proof is built on: a wrap proof wraps one step proof; a step
-- | proof verifies, per slot in slot order, a wrap proof — or nothing on
-- | a base-case slot, whose dummy proof is not cached.
data Links
  = Wraps ProofRef
  | Verifies (Array (Maybe ProofRef))

-- | One cached proof: the verification key's JSON, the proof's serde
-- | JSON and the proofs it is built on.
type Entry = { vk :: String, proof :: String, links :: Links }

-- | An entry on disk: the links as a `step` key on a wrap proof and a
-- | `prevs` key on a step proof.
type EntryJson =
  { vk :: String
  , proof :: String
  , step :: Maybe ProofRef
  , prevs :: Maybe (Array (Maybe ProofRef))
  }

toJson :: Entry -> EntryJson
toJson e = case e.links of
  Wraps step -> { vk: e.vk, proof: e.proof, step: Just step, prevs: Nothing }
  Verifies prevs -> { vk: e.vk, proof: e.proof, step: Nothing, prevs: Just prevs }

-- | An on-disk entry carries exactly one kind of link; anything else is
-- | decode drift and reads as a miss.
fromJson :: EntryJson -> Maybe Entry
fromJson j = case j.step, j.prevs of
  Just step, Nothing -> Just { vk: j.vk, proof: j.proof, links: Wraps step }
  Nothing, Just prevs -> Just { vk: j.vk, proof: j.proof, links: Verifies prevs }
  _, _ -> Nothing

type Store = Object (Object Entry)

-- | On-disk shape: `{ "<vkDigest>": { "<publicInput>": EntryJson } }`.
type StoreJson = Object (Object EntryJson)

-- | Load the store. Missing file or any decode drift => empty store
-- | (a miss); the proof is simply regenerated. A cache must always be
-- | reconstructible from empty. Buckets whose key is not a decimal digest
-- | are dropped, so a store written under an older keying cannot survive
-- | the next save beside the new one.
loadStore :: String -> Effect Store
loadStore path = do
  present <- exists path
  if not present then pure Object.empty
  else do
    txt <- readTextFile UTF8 path
    let
      buckets = Object.filterKeys (isJust <<< BigInt.fromString)
        (fromMaybe Object.empty (JSON.readJSON_ txt :: Maybe StoreJson))
      entries = Object.fromFoldable <<< mapMaybe (\(Tuple k j) -> Tuple k <$> fromJson j) <<< Object.toUnfoldable
    pure (map entries buckets)

-- | Write the store through, creating the containing directory if
-- | needed (recursive mkdir is idempotent — no throw if it exists).
saveStore :: String -> Store -> Effect Unit
saveStore path store = do
  case lastIndexOf (Pattern "/") path of
    Just i -> mkdir' (take i path) { recursive: true, mode: permsAll }
    Nothing -> pure unit
  writeTextFile UTF8 path (JSON.writeJSON (map (map toJson) store :: StoreJson))

getEntry :: ProofCache -> String -> String -> Effect (Maybe Entry)
getEntry (ProofCache path) vk pi = do
  store <- loadStore path
  pure (Object.lookup vk store >>= Object.lookup pi)

setEntry :: ProofCache -> String -> String -> Entry -> Effect Unit
setEntry (ProofCache path) vkDigest pi entry = do
  store <- loadStore path
  let inner = fromMaybe Object.empty (Object.lookup vkDigest store)
  saveStore path (Object.insert vkDigest (Object.insert pi entry inner) store)

-- | Canonical, deterministic string for a field element (its integer
-- | value). Stable across runs/machines.
fieldStr :: forall f. PrimeField f => f -> String
fieldStr = show <<< toBigInt

-- | Public-input field vector → its canonical key (OCaml keys by
-- | `[%to_yojson: Field.t array]`; same content, our string form).
piKey :: forall f. PrimeField f => Array f -> String
piKey = joinWith "," <<< map fieldStr

-- | Cache lookup / store for `pallas*` proofs (Vesta.G commitments,
-- | Pallas-base-field scalars — what pickles' Tick / Step side produces).
-- | The key is the verification key's digest, as a decimal string; a step
-- | proof records the wrap proofs it verified.
getPallasProof
  :: ProofCache
  -> String
  -> Array Pallas.BaseField
  -> Effect (Maybe (Proof Vesta.G Pallas.BaseField))
getPallasProof cache vkDigest pis = do
  m <- getEntry cache vkDigest (piKey pis)
  pure (pallasProofFromSerdeJson <<< _.proof <$> m)

setPallasProof
  :: ProofCache
  -> String
  -> VerifierIndex Vesta.G Pallas.BaseField
  -> Array Pallas.BaseField
  -> Proof Vesta.G Pallas.BaseField
  -> Array (Maybe ProofRef)
  -> Effect Unit
setPallasProof cache vkDigest vk pis proof prevs =
  setEntry cache vkDigest (piKey pis)
    { vk: pallasVerifierIndexJsonKey vk
    , proof: pallasProofToSerdeJson proof
    , links: Verifies prevs
    }

-- | Cache lookup / store for `vesta*` proofs (Pallas.G commitments,
-- | Vesta-base-field scalars — what pickles' Tock / Wrap side produces).
-- | A wrap proof records the step proof it wrapped.
getVestaProof
  :: ProofCache
  -> String
  -> Array Vesta.BaseField
  -> Effect (Maybe (Proof Pallas.G Vesta.BaseField))
getVestaProof cache vkDigest pis = do
  m <- getEntry cache vkDigest (piKey pis)
  pure (vestaProofFromSerdeJson <<< _.proof <$> m)

setVestaProof
  :: ProofCache
  -> String
  -> VerifierIndex Pallas.G Vesta.BaseField
  -> Array Vesta.BaseField
  -> Proof Pallas.G Vesta.BaseField
  -> ProofRef
  -> Effect Unit
setVestaProof cache vkDigest vk pis proof step =
  setEntry cache vkDigest (piKey pis)
    { vk: vestaVerifierIndexJsonKey vk
    , proof: vestaProofToSerdeJson proof
    , links: Wraps step
    }

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
-- Both renderers are exported: they produce an entry's `vk` field, and the
-- digest-equality test consumes the Vesta one. The `VkRaw`/helper types stay
-- private to this module.
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
