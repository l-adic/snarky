module Test.Pickles.Step.ChallengeDigest
  ( spec
  ) where

-- | Tests for challenge digest circuit.

import Prelude

import Data.Fin (getFinite)
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Traversable (for_)
import Data.Tuple (Tuple(..))
import Data.Vector (nil, (:<))
import Data.Vector as Vector
import Partial.Unsafe (unsafePartial)
import Pickles.Sponge (evalPureSpongeM, evalSpongeM, initialSponge, initialSpongeCircuit)
import Pickles.Sponge as Sponge
import Pickles.Step.ChallengeDigest (ChallengeDigestInput, challengeDigestCircuit)
import Pickles.Step.Types (BulletproofChallenges)
import RandomOracle.Sponge (Sponge)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky)
import Snarky.Circuit.DSL as SizedF
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (fromInt)
import Snarky.Curves.Vesta as Vesta
import Test.Snarky.Circuit.Utils (circuitSpecPureInputs, satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-------------------------------------------------------------------------------
-- | Types
-------------------------------------------------------------------------------

type StepField = Vesta.ScalarField

-- | Value type for test input (1 previous proof)
type ChallengeDigestTestInput1 =
  ChallengeDigestInput 1 (F StepField) Boolean

-- | Variable type for circuit
type ChallengeDigestTestInputVar1 =
  ChallengeDigestInput 1 (FVar StepField) (BoolVar StepField)

-------------------------------------------------------------------------------
-- | Pure Reference Implementation
-------------------------------------------------------------------------------

-- | Pure version of challenge digest for reference.
-- | Conditionally absorbs challenges based on mask, then squeezes.
challengeDigestPure
  :: forall n
   . ChallengeDigestInput n (F StepField) Boolean
  -> F StepField
challengeDigestPure { mask, oldChallenges } =
  let
    sponge :: Sponge StepField
    sponge = coerce (initialSponge :: Sponge (F StepField))

    result :: StepField
    result = evalPureSpongeM sponge do
      -- Absorb challenges conditionally
      for_ (Vector.zip mask oldChallenges) \(Tuple keep chals) ->
        when keep do
          -- Absorb all 16 scalar challenges
          for_ chals \chal ->
            Sponge.absorb (coerce (SizedF.toField chal) :: StepField)
      -- Squeeze to get digest
      Sponge.squeeze
  in
    F result

-------------------------------------------------------------------------------
-- | Test Circuit
-------------------------------------------------------------------------------

-- | The circuit under test: runs challengeDigestCircuit and returns the digest
testCircuit1
  :: forall t
   . CircuitM StepField (KimchiConstraint StepField) t Identity
  => ChallengeDigestTestInputVar1
  -> Snarky (KimchiConstraint StepField) t Identity (FVar StepField)
testCircuit1 input =
  evalSpongeM initialSpongeCircuit (challengeDigestCircuit input)

-------------------------------------------------------------------------------
-- | Test Inputs
-------------------------------------------------------------------------------

-- | Generate dummy scalar challenges (all zeros)
dummyBulletproofChallenges :: BulletproofChallenges (F StepField)
dummyBulletproofChallenges = Vector.generate \_ ->
  unsafePartial fromJust $ SizedF.fromField (F zero)

-- | Generate non-zero scalar challenges for testing
nonZeroBulletproofChallenges :: BulletproofChallenges (F StepField)
nonZeroBulletproofChallenges = Vector.generate \i ->
  unsafePartial fromJust $ SizedF.fromField (F $ fromInt (getFinite i + 1))

-------------------------------------------------------------------------------
-- | Tests
-------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "Pickles.Step.ChallengeDigest" do
  describe "challengeDigestCircuit" do
    it "produces correct digest with mask=true (absorbs challenges)" do
      let
        input :: ChallengeDigestTestInput1
        input =
          { mask: true :< nil
          , oldChallenges: nonZeroBulletproofChallenges :< nil
          }

        -- Test function: given input, return expected output
        testFn :: ChallengeDigestTestInput1 -> F StepField
        testFn i = challengeDigestPure i

      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @ChallengeDigestTestInput1)
            (Proxy @(F StepField))
            (Proxy @(KimchiConstraint StepField))
            testCircuit1
            Kimchi.initialState
        , checker: Kimchi.eval
        , solver: makeSolver (Proxy @(KimchiConstraint StepField)) testCircuit1
        , testFunction: satisfied testFn
        , postCondition: Kimchi.postCondition
        }
        [ input ]

    it "produces correct digest with mask=false (skips challenges)" do
      let
        input :: ChallengeDigestTestInput1
        input =
          { mask: false :< nil
          , oldChallenges: nonZeroBulletproofChallenges :< nil
          }

        -- Test function: given input, return expected output
        testFn :: ChallengeDigestTestInput1 -> F StepField
        testFn i = challengeDigestPure i

      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @ChallengeDigestTestInput1)
            (Proxy @(F StepField))
            (Proxy @(KimchiConstraint StepField))
            testCircuit1
            Kimchi.initialState
        , checker: Kimchi.eval
        , solver: makeSolver (Proxy @(KimchiConstraint StepField)) testCircuit1
        , testFunction: satisfied testFn
        , postCondition: Kimchi.postCondition
        }
        [ input ]

    it "circuit matches pure implementation for dummy challenges" do
      -- Note: Absorbing zeros still changes sponge state due to permutation.
      -- This test verifies the circuit outputs match the pure impl for both cases.
      let
        inputTrue :: ChallengeDigestTestInput1
        inputTrue =
          { mask: true :< nil
          , oldChallenges: dummyBulletproofChallenges :< nil
          }

        inputFalse :: ChallengeDigestTestInput1
        inputFalse =
          { mask: false :< nil
          , oldChallenges: dummyBulletproofChallenges :< nil
          }

        -- Test function: given input, return expected output
        testFn :: ChallengeDigestTestInput1 -> F StepField
        testFn i = challengeDigestPure i

      circuitSpecPureInputs
        { builtState: compilePure
            (Proxy @ChallengeDigestTestInput1)
            (Proxy @(F StepField))
            (Proxy @(KimchiConstraint StepField))
            testCircuit1
            Kimchi.initialState
        , checker: Kimchi.eval
        , solver: makeSolver (Proxy @(KimchiConstraint StepField)) testCircuit1
        , testFunction: satisfied testFn
        , postCondition: Kimchi.postCondition
        }
        [ inputTrue, inputFalse ]
