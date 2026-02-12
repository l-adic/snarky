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
  , dummyProofWitness
  , dummyFinalizeOtherProofParams
  ) where

import Prelude

import Data.Maybe (fromJust)
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Linearization.Types (mkLinearizationPoly)
import Pickles.Step.FinalizeOtherProof (FinalizeOtherProofParams)
import Pickles.ProofWitness (AllEvals, DomainValues, ProofWitness)
import Pickles.Verify.Types (BulletproofChallenges, DeferredValues, PlonkMinimal, ScalarChallenge, UnfinalizedProof)
import Snarky.Circuit.DSL as SizedF
import Snarky.Circuit.Kimchi (class Shifted, toShifted)
import Snarky.Circuit.Types (F)
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField)

-- | A dummy 128-bit scalar challenge (all zeros).
dummyScalarChallenge :: forall @f. PrimeField f => FieldSizeInBits f 255 => ScalarChallenge f
dummyScalarChallenge = unsafePartial fromJust $ SizedF.fromField @128 zero

-- | Dummy bulletproof challenges (16 zero challenges).
dummyBulletproofChallenges :: forall @f. PrimeField f => FieldSizeInBits f 255 => BulletproofChallenges f
dummyBulletproofChallenges = Vector.generate \_ -> dummyScalarChallenge @f

-- | Dummy PLONK challenges (all zeros).
dummyPlonkMinimal :: forall @f. PrimeField f => FieldSizeInBits f 255 => PlonkMinimal f
dummyPlonkMinimal =
  { alpha: dummyScalarChallenge @f
  , beta: dummyScalarChallenge @f
  , gamma: dummyScalarChallenge @f
  , zeta: dummyScalarChallenge @f
  }

-- | Dummy deferred values for bootstrapping.
-- | Note: We use shifted 'one' because shifted 'zero' is often a forbidden value in these protocols.
dummyDeferredValues :: forall @f @f_other @sf. PrimeField f => PrimeField f_other => FieldSizeInBits f 255 => Shifted (F f_other) sf => DeferredValues (F f) sf
dummyDeferredValues =
  let
    oneSf = toShifted (one :: F f_other)
  in
    { plonk: dummyPlonkMinimal @(F f)
    , combinedInnerProduct: oneSf
    , xi: dummyScalarChallenge @(F f)
    , bulletproofChallenges: dummyBulletproofChallenges @(F f)
    , b: oneSf
    , perm: oneSf
    , zetaToSrsLength: oneSf
    , zetaToDomainSize: oneSf
    }

-- | Dummy unfinalized proof for bootstrapping.
dummyUnfinalizedProof :: forall @f @f_other @sf. PrimeField f => PrimeField f_other => FieldSizeInBits f 255 => Shifted (F f_other) sf => UnfinalizedProof (F f) sf Boolean
dummyUnfinalizedProof =
  { deferredValues: dummyDeferredValues @f @f_other @sf
  , shouldFinalize: false
  , spongeDigestBeforeEvaluations: zero
  }

-------------------------------------------------------------------------------
-- | Dummy Proof Witness
-------------------------------------------------------------------------------

dummyPointEval :: forall f. PrimeField f => { zeta :: f, omegaTimesZeta :: f }
dummyPointEval = { zeta: zero, omegaTimesZeta: zero }

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

dummyDomainValues :: forall f. PrimeField f => DomainValues f
dummyDomainValues =
  { zkPolynomial: zero
  , zetaToNMinus1: zero
  , omegaToMinusZkRows: zero
  , vanishesOnZk: zero
  , lagrangeFalse0: zero
  , lagrangeTrue1: zero
  }

dummyProofWitness :: forall f. PrimeField f => ProofWitness f
dummyProofWitness =
  { allEvals: dummyAllEvals
  , domainValues: dummyDomainValues
  , publicEvalForFt: zero
  }

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
