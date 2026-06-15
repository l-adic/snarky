-- | Shared helper for exercising `Pickles.Prove.SerializeProof` across the
-- | recursive prove tests: round-trip every proof used as a recursive prev. If
-- | reconstruction is faithful the downstream proof is unchanged, so the test's
-- | existing verify/equality assertions still hold — at zero extra proving.
-- |
-- | Two flavours: `roundTripAndVerify` exercises the in-memory transform
-- | (`toSerializableCompiledProof`/`reconstructCompiledProof`), used by every
-- | prove test; `roundTripJSONAndVerify` additionally goes through the JSON
-- | `encodeCompiledProof`/`decodeCompiledProof` Sendability codec, used where the
-- | statement type is serializable (e.g. SimpleChain over `NoOutput`).
module Test.Pickles.SerializeRoundTrip
  ( module Pickles.Prove.SerializeProof
  , roundTrip
  , roundTripAndVerify
  , roundTripJSON
  , roundTripJSONAndVerify
  ) where

import Prelude

import Data.Either (either)
import Effect.Aff.Class (class MonadAff, liftAff)
import Partial.Unsafe (unsafeCrashWith)
import Pickles.Prove.SerializeProof (WidthDummies, decodeCompiledProof, encodeCompiledProof, mkWidthDummies, reconstructCompiledProof, toSerializableCompiledProof)
import Pickles.Verify (CompiledProof, Verifier, toVerifiable, verifyBatch)
import Simple.JSON (class ReadForeign, class WriteForeign)
import Test.Spec.Assertions (shouldEqual)

-- | Serialize a `CompiledProof` and reconstruct it (in memory) — the identity
-- | if reconstruction is faithful.
roundTrip
  :: forall mpv stmt
   . WidthDummies
  -> CompiledProof mpv stmt
  -> CompiledProof mpv stmt
roundTrip dummies = reconstructCompiledProof dummies <<< toSerializableCompiledProof

-- | As `roundTrip`, but through the JSON `encodeCompiledProof`/
-- | `decodeCompiledProof` codec (which subsume the in-memory transform).
-- | Requires a serializable statement; a decode failure crashes the test.
roundTripJSON
  :: forall mpv stmt
   . WriteForeign stmt
  => ReadForeign stmt
  => WidthDummies
  -> CompiledProof mpv stmt
  -> CompiledProof mpv stmt
roundTripJSON dummies =
  either (unsafeCrashWith <<< show) identity <<< decodeCompiledProof dummies <<< encodeCompiledProof

-- | Round-trip a proof, assert the reconstruction still verifies standalone, and
-- | return it for downstream use as a recursive prev. Splitting the round-trip
-- | out as an explicit, asserted step documents that the test exercises
-- | serialize → reconstruct, and the subsequent use-as-prev is the
-- | byte-faithfulness check.
roundTripAndVerify
  :: forall mpv stmt m
   . MonadAff m
  => WidthDummies
  -> Verifier
  -> CompiledProof mpv stmt
  -> m (CompiledProof mpv stmt)
roundTripAndVerify dummies verifier cp = do
  let cp' = roundTrip dummies cp
  liftAff (verifyBatch verifier [ toVerifiable cp' ] `shouldEqual` true)
  pure cp'

-- | As `roundTripAndVerify`, but through the JSON codec.
roundTripJSONAndVerify
  :: forall mpv stmt m
   . MonadAff m
  => WriteForeign stmt
  => ReadForeign stmt
  => WidthDummies
  -> Verifier
  -> CompiledProof mpv stmt
  -> m (CompiledProof mpv stmt)
roundTripJSONAndVerify dummies verifier cp = do
  let cp' = roundTripJSON dummies cp
  liftAff (verifyBatch verifier [ toVerifiable cp' ] `shouldEqual` true)
  pure cp'
