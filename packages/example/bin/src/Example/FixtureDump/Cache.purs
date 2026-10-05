-- | Collect only the step and wrap entries produced by each job. Workers
-- | read seed copies and write separate files; the host publishes their union.
module Example.FixtureDump.Cache (Store, readStore, proofEntries, combine) where

import Prelude

import Data.Array as Array
import Data.Either (either)
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..), maybe)
import Data.Traversable (traverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Foreign (Foreign)
import Foreign.Object (Object)
import Foreign.Object as Object
import Node.Encoding (Encoding(..))
import Node.FS.Sync as FS
import Pickles.Verify (CompiledProof(..))
import Simple.JSON as JSON
import Snarky.Backend.Kimchi.Proof (vestaProofToSerdeJson)
import Snarky.Backend.Kimchi.ProofCache (ProofRef)
import Snarky.Example.Snark.Work (Proof)

type Store = Object (Object Foreign)

readStore :: String -> Effect Store
readStore path = do
  present <- FS.exists path
  if present then do
    text <- FS.readTextFile UTF8 path
    either (throw <<< show) pure (JSON.readJSON text)
  else pure Object.empty

proofEntries :: String -> Proof -> Effect Store
proofEntries path (CompiledProof proof) = do
  store <- readStore path
  let
    entries = do
      Tuple vkDigest bucket <- Object.toUnfoldable store :: Array _
      Tuple publicInput entry <- Object.toUnfoldable bucket :: Array _
      pure { ref: { vkDigest, publicInput }, entry }
  candidates <- traverse
    ( \e -> do
        header <-
          either (throw <<< show) pure (JSON.read e.entry)
            :: Effect { proof :: String, step :: Maybe ProofRef }
        pure { ref: e.ref, entry: e.entry, header }
    )
    entries
  case Array.filter (\e -> e.header.proof == vestaProofToSerdeJson proof.wrapProof) candidates of
    [ e ] -> case e.header.step of
      Nothing -> throw "the produced wrap proof has no step reference"
      Just step -> do
        entry <- maybe (throw "the produced proof's step entry is missing") pure
          (Object.lookup step.vkDigest store >>= Object.lookup step.publicInput)
        combine [ singleton e.ref e.entry, singleton step entry ]
    _ -> throw "expected exactly one cache entry for the produced wrap proof"

singleton :: ProofRef -> Foreign -> Store
singleton ref entry = Object.singleton ref.vkDigest (Object.singleton ref.publicInput entry)

combine :: Array Store -> Effect Store
combine stores = foldM addStore Object.empty stores
  where
  addStore acc store = foldM addBucket acc (Object.toUnfoldable store :: Array _)
  addBucket acc (Tuple vk bucket) = foldM (addEntry vk) acc (Object.toUnfoldable bucket :: Array _)
  addEntry vk acc (Tuple pi entry) = do
    let bucket = maybe Object.empty identity (Object.lookup vk acc)
    case Object.lookup pi bucket of
      Just old | JSON.writeJSON old /= JSON.writeJSON entry -> throw "conflicting fixture cache entries"
      _ -> pure (Object.insert vk (Object.insert pi entry bucket) acc)
