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
  ) where

import Prelude

import Data.Maybe (Maybe(..), fromMaybe)
import Data.String (Pattern(..), lastIndexOf, take)
import Data.String.Common (joinWith)
import Effect (Effect)
import Foreign.Object (Object)
import Foreign.Object as Object
import Node.Encoding (Encoding(..))
import Node.FS.Perms (permsAll)
import Node.FS.Sync (exists, mkdir', readTextFile, writeTextFile)
import Pickles.Field (StepField, WrapField)
import Pickles.ProofFFI (Proof, pallasVerifierIndexDigest, vestaVerifierIndexDigest)
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

stepVkKey :: VerifierIndex Vesta.G Pallas.BaseField -> String
stepVkKey vk = "step:" <> fieldStr (pallasVerifierIndexDigest vk)

wrapVkKey :: VerifierIndex Pallas.G Vesta.BaseField -> String
wrapVkKey vk = "wrap:" <> fieldStr (vestaVerifierIndexDigest vk)

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
