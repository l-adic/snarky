-- | Lets the recursive prove tests exercise
-- | `Pickles.Prove.SerializeProof` for free: a proof round-tripped
-- | before being used as a prev leaves the chain unchanged if
-- | reconstruction is faithful, so the tests' own assertions carry the
-- | round trip too.
-- |
-- | `roundTripAndVerify` goes through the in-memory transform;
-- | `roundTripJSONAndVerify` goes through the JSON codec as well, and
-- | needs a serializable statement.
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
import Pickles.Field (StepField)
import Pickles.Prove.SerializeProof (WidthDummies, decodeCompiledProof, encodeCompiledProof, mkWidthDummies, reconstructCompiledProof, toSerializableCompiledProof)
import Pickles.Verify (CompiledProof, Verifier, toVerifiable, verifyBatch)
import Simple.JSON (class ReadForeign, class WriteForeign)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.Types (class CircuitType)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Test.Spec.Assertions (shouldEqual)

-- | The SRSes the JSON decode needs, left open so a test can pass its
-- | whole environment.
type Srs r = { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG | r }

-- | Serialize a `CompiledProof` and reconstruct it in memory — the
-- | identity, if reconstruction is faithful.
roundTrip
  :: forall mpv stmt stmtVar
   . CircuitType StepField stmt stmtVar
  => WidthDummies
  -> CompiledProof mpv stmt
  -> CompiledProof mpv stmt
roundTrip dummies = reconstructCompiledProof dummies <<< toSerializableCompiledProof

-- | As `roundTrip`, but through the JSON codec, which subsumes the
-- | in-memory transform. A decode failure crashes the test.
roundTripJSON
  :: forall mpv stmt stmtVar r
   . WriteForeign stmt
  => ReadForeign stmt
  => CircuitType StepField stmt stmtVar
  => Srs r
  -> CompiledProof mpv stmt
  -> CompiledProof mpv stmt
roundTripJSON srs =
  either (unsafeCrashWith <<< show) identity <<< decodeCompiledProof srs <<< encodeCompiledProof

-- | Round-trip a proof, assert the reconstruction verifies on its own,
-- | and return it for use as a recursive prev, which is the stricter
-- | check.
roundTripAndVerify
  :: forall mpv stmt stmtVar m
   . MonadAff m
  => CircuitType StepField stmt stmtVar
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
  :: forall mpv stmt stmtVar m r
   . MonadAff m
  => WriteForeign stmt
  => ReadForeign stmt
  => CircuitType StepField stmt stmtVar
  => Srs r
  -> Verifier
  -> CompiledProof mpv stmt
  -> m (CompiledProof mpv stmt)
roundTripJSONAndVerify srs verifier cp = do
  let cp' = roundTripJSON srs cp
  liftAff (verifyBatch verifier [ toVerifiable cp' ] `shouldEqual` true)
  pure cp'
