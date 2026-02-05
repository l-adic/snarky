-- | Dummy values for bootstrapping Pickles recursion.
-- |
-- | At the base case (Step0), there are no real previous Wrap proofs to verify.
-- | The circuit uses dummy unfinalized proofs with `shouldFinalize = false`.
-- | This makes the assertion `finalized || not shouldFinalize` pass regardless
-- | of the dummy's actual verification result.
-- |
-- | Reference: mina/src/lib/pickles/unfinalized.ml:25-104, dummy.ml
module Pickles.Step.Dummy
  ( dummyScalarChallenge
  , dummyBulletproofChallenges
  , dummyPlonkMinimal
  , dummyDeferredValues
  , dummyUnfinalizedProof
  ) where

import Prelude

import Data.Vector as Vector
import Pickles.Step.Types (BulletproofChallenges, DeferredValues, PlonkMinimal, ScalarChallenge, UnfinalizedProof)
import Snarky.Curves.Class (class PrimeField)
import Snarky.Data.SizedF (SizedF(..))
import Snarky.Types.Shifted (Type1(..))

-------------------------------------------------------------------------------
-- | Dummy Scalar Challenge
-------------------------------------------------------------------------------

-- | A dummy 128-bit scalar challenge (all zeros).
-- |
-- | In the real OCaml code, dummy challenges are generated randomly via `Ro.scalar_chal()`.
-- | For simplicity, we use zero. The value doesn't matter since `shouldFinalize = false`.
dummyScalarChallenge :: forall f. PrimeField f => ScalarChallenge f
dummyScalarChallenge = SizedF zero

-------------------------------------------------------------------------------
-- | Dummy Bulletproof Challenges
-------------------------------------------------------------------------------

-- | Dummy bulletproof challenges (16 zero challenges).
-- |
-- | Reference: dummy.ml:31-34 `Ipa.Wrap.challenges`
dummyBulletproofChallenges :: forall f. PrimeField f => BulletproofChallenges f
dummyBulletproofChallenges = Vector.generate \_ -> dummyScalarChallenge

-------------------------------------------------------------------------------
-- | Dummy Plonk Minimal
-------------------------------------------------------------------------------

-- | Dummy PLONK challenges (all zeros).
-- |
-- | Reference: unfinalized.ml:33-42
dummyPlonkMinimal :: forall f. PrimeField f => PlonkMinimal f
dummyPlonkMinimal =
  { alpha: dummyScalarChallenge
  , beta: zero
  , gamma: zero
  , zeta: dummyScalarChallenge
  }

-------------------------------------------------------------------------------
-- | Dummy Deferred Values
-------------------------------------------------------------------------------

-- | Dummy deferred values for bootstrapping.
-- |
-- | Uses Type1 shifted values (for Step verifying Wrap).
-- | All values are zero, which is fine since `shouldFinalize = false`.
-- |
-- | Reference: unfinalized.ml:95-101
dummyDeferredValues :: forall f. PrimeField f => DeferredValues f (Type1 f)
dummyDeferredValues =
  { plonk: dummyPlonkMinimal
  , combinedInnerProduct: Type1 zero
  , xi: dummyScalarChallenge
  , bulletproofChallenges: dummyBulletproofChallenges
  , b: Type1 zero
  , perm: Type1 zero
  }

-------------------------------------------------------------------------------
-- | Dummy Unfinalized Proof
-------------------------------------------------------------------------------

-- | Dummy unfinalized proof for bootstrapping.
-- |
-- | The key is `shouldFinalize = false`, which makes the circuit's
-- | assertion `finalized || not shouldFinalize` pass regardless of
-- | whether the dummy values actually verify.
-- |
-- | Reference: unfinalized.ml:102 `should_finalize = false`
dummyUnfinalizedProof :: forall f. PrimeField f => UnfinalizedProof f (Type1 f) Boolean
dummyUnfinalizedProof =
  { deferredValues: dummyDeferredValues
  , shouldFinalize: false
  , spongeDigestBeforeEvaluations: zero
  }
