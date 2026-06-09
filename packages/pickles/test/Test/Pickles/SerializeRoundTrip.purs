-- | Shared helper for exercising `Pickles.Prove.SerializeProof` across the
-- | recursive prove tests: round-trip every proof used as a recursive prev
-- | through `toSerializableCompiledProof`/`reconstructCompiledProof`. If
-- | reconstruction is faithful the downstream proof is unchanged, so the
-- | test's existing verify/equality assertions still hold — at zero extra
-- | proving.
module Test.Pickles.SerializeRoundTrip
  ( mkWidthDummies
  , roundTrip
  , roundTripAndVerify
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow)
import Effect.Exception (Error)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Prove.SerializeProof (WidthDummies, reconstructCompiledProof, toSerializableCompiledProof)
import Pickles.Step.Dummy (baseCaseDummies, computeDummySgValues)
import Pickles.Verify (CompiledProof, Verifier, toVerifiable, verifyBatch)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Test.Spec.Assertions (shouldEqual)

-- | The front-padding dummies the prover packs into `widthData` at the
-- | `CompiledProof` construction site (Compile.purs): `dummyIpaChallenges`
-- | for the bp-challenge stacks and the `maxProofsVerified: 0` dummy wrap sg
-- | for the outer-step challenge-polynomial commitment. All constants of the
-- | SRS — independent of any program's `mpvMax`.
mkWidthDummies :: CRS PallasG -> CRS VestaG -> WidthDummies
mkWidthDummies pallasSrs vestaSrs =
  let
    dummySgsMax = computeDummySgValues (baseCaseDummies { maxProofsVerified: 0 }) pallasSrs vestaSrs
  in
    { dummyOldBp: dummyIpaChallenges.stepExpanded
    , dummyMsgWrap: dummyIpaChallenges.wrapExpanded
    , dummyChalPolyComm: dummySgsMax.ipa.wrap.sg
    }

-- | Serialize a `CompiledProof` and reconstruct it — the identity if
-- | reconstruction is faithful. Wrap any recursive prev in this to exercise
-- | the round-trip in place.
roundTrip
  :: forall mpv stmt
   . WidthDummies
  -> CompiledProof mpv stmt
  -> CompiledProof mpv stmt
roundTrip dummies = reconstructCompiledProof dummies <<< toSerializableCompiledProof

-- | Round-trip a proof through SerializeProof, assert the reconstruction still
-- | verifies standalone, and return it for downstream use as a recursive prev.
-- | Splitting the round-trip out as an explicit, asserted step (rather than
-- | inlining it at the `InductivePrev` call site) documents that the test is
-- | exercising serialize → reconstruct, and the subsequent use-as-prev is the
-- | byte-faithfulness check.
roundTripAndVerify
  :: forall mpv stmt m
   . MonadThrow Error m
  => WidthDummies
  -> Verifier
  -> CompiledProof mpv stmt
  -> m (CompiledProof mpv stmt)
roundTripAndVerify dummies verifier cp = do
  let cp' = roundTrip dummies cp
  verifyBatch verifier [ toVerifiable cp' ] `shouldEqual` true
  pure cp'
