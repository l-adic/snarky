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
  , dummyWrapProofWitness
  , dummyFinalizeOtherProofParams
  ) where

import Prelude

import Data.Maybe (fromJust)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Types (mkLinearizationPoly)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofParams)
import Pickles.Step.Types (BulletproofChallenges, DeferredValues, PlonkMinimal, ScalarChallenge, UnfinalizedProof)
import Pickles.Step.WrapProofWitness (AllEvals, DomainValues, WrapProofWitness)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi (class Shifted, toShifted)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)

-------------------------------------------------------------------------------
-- | Dummy Scalar Challenge
-------------------------------------------------------------------------------

-- | A dummy 128-bit scalar challenge (all zeros).
-- |
-- | In the real OCaml code, dummy challenges are generated randomly via `Ro.scalar_chal()`.
-- | For simplicity, we use zero. The value doesn't matter since `shouldFinalize = false`.
dummyScalarChallenge :: forall f. PrimeField f => FieldSizeInBits f 255 => ScalarChallenge f
dummyScalarChallenge = unsafePartial fromJust $ SizedF.fromField @128 zero

-------------------------------------------------------------------------------
-- | Dummy Bulletproof Challenges
-------------------------------------------------------------------------------

-- | Dummy bulletproof challenges (16 zero challenges).
-- |
-- | Reference: dummy.ml:31-34 `Ipa.Wrap.challenges`
dummyBulletproofChallenges :: forall f. PrimeField f => FieldSizeInBits f 255 => BulletproofChallenges f
dummyBulletproofChallenges = Vector.generate \_ -> dummyScalarChallenge

-------------------------------------------------------------------------------
-- | Dummy Plonk Minimal
-------------------------------------------------------------------------------

-- | Dummy PLONK challenges (all zeros).
-- |
-- | Reference: unfinalized.ml:33-42
dummyPlonkMinimal :: forall f. PrimeField f => FieldSizeInBits f 255 => PlonkMinimal f
dummyPlonkMinimal =
  { alpha: dummyScalarChallenge
  , beta: dummyScalarChallenge
  , gamma: dummyScalarChallenge
  , zeta: dummyScalarChallenge
  }

-------------------------------------------------------------------------------
-- | Dummy Deferred Values
-------------------------------------------------------------------------------

-- | Dummy deferred values for bootstrapping.
-- |
-- | All shifted values are `toShifted zero`. The actual values don't matter
-- | since `shouldFinalize = false` bypasses verification.
-- |
-- | Reference: unfinalized.ml:95-101
dummyDeferredValues :: forall f sf. PrimeField f => FieldSizeInBits f 255 => Shifted f sf => DeferredValues f sf
dummyDeferredValues =
  let zeroSf = toShifted (zero :: f)
  in
    { plonk: dummyPlonkMinimal
    , combinedInnerProduct: zeroSf
    , xi: dummyScalarChallenge
    , bulletproofChallenges: dummyBulletproofChallenges
    , b: zeroSf
    , perm: zeroSf
    , zetaToSrsLength: zeroSf
    , zetaToDomainSize: zeroSf
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
dummyUnfinalizedProof :: forall f sf. PrimeField f => FieldSizeInBits f 255 => Shifted f sf => UnfinalizedProof f sf Boolean
dummyUnfinalizedProof =
  { deferredValues: dummyDeferredValues
  , shouldFinalize: false
  , spongeDigestBeforeEvaluations: zero
  }

-------------------------------------------------------------------------------
-- | Dummy Wrap Proof Witness
-------------------------------------------------------------------------------

-- | Dummy point evaluation (both zeta and zeta*omega are zero).
dummyPointEval :: forall f. PrimeField f => { zeta :: f, omegaTimesZeta :: f }
dummyPointEval = { zeta: zero, omegaTimesZeta: zero }

-- | Dummy all evaluations.
dummyAllEvals :: forall f. PrimeField f => AllEvals f
dummyAllEvals =
  { ftEval1: zero
  , publicEvals: dummyPointEval
  , zEvals: dummyPointEval
  , indexEvals: Vector.generate \_ -> dummyPointEval
  , witnessEvals: Vector.generate \_ -> dummyPointEval
  , coeffEvals: Vector.generate \_ -> dummyPointEval
  , sigmaEvals: Vector.generate \_ -> dummyPointEval
  }

-- | Dummy domain values (all zeros).
dummyDomainValues :: forall f. PrimeField f => DomainValues f
dummyDomainValues =
  { zkPolynomial: zero
  , zetaToNMinus1: zero
  , omegaToMinusZkRows: zero
  , vanishesOnZk: zero
  , lagrangeFalse0: zero
  , lagrangeTrue1: zero
  }

-- | Dummy wrap proof witness for bootstrapping.
-- |
-- | Contains polynomial evaluations, domain values, and public eval (all zeros).
-- | This is fine since `shouldFinalize = false` makes verification pass.
dummyWrapProofWitness :: forall f. PrimeField f => WrapProofWitness f
dummyWrapProofWitness =
  { allEvals: dummyAllEvals
  , domainValues: dummyDomainValues
  , publicEvalForFt: zero
  }

-------------------------------------------------------------------------------
-- | Dummy FinalizeOtherProofParams
-------------------------------------------------------------------------------

-- | Dummy compile-time parameters for bootstrapping.
-- |
-- | All values are zero. This is fine for the base case where
-- | `shouldFinalize = false` makes verification pass regardless.
dummyFinalizeOtherProofParams :: forall f. PrimeField f => FinalizeOtherProofParams f
dummyFinalizeOtherProofParams =
  { domain:
      { generator: zero
      , shifts: Vector.generate \_ -> zero
      }
  , endo: zero
  , zkRows: 0
  , linearizationPoly: mkLinearizationPoly []
  }
