module Test.Snarky.Circuit.Kimchi.EndoScale where

import Prelude

import Data.Identity (Identity)
import Data.Traversable (foldl)
import JS.BigInt (fromInt) as BigInt
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky, const_)
import Snarky.Circuit.Kimchi.EndoScale (ScalarChallenge(..), toField)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class HasEndo, endoBase, endoScalar, fromBigInt, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.QuickCheck.Gen as Gen
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- Test input: scalar challenge value (always 128 bits)
type TestInput = F Vesta.ScalarField

-- Reference implementation: Just return the input (the circuit should reconstruct it)
refEndoScale :: TestInput -> TestInput
refEndoScale input = input

-- Circuit implementation: decompose scalar and reconstruct it
circuit
  :: forall t
   . CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t Identity
  => FVar Vesta.ScalarField
  -> Snarky (KimchiConstraint Vesta.ScalarField) t Identity (FVar Vesta.ScalarField)
circuit scalarVar = do
  let challenge = ScalarChallenge scalarVar
  -- Use endoBase which gives us the endomorphism coefficient in the same field
  let endoCoeff = endoBase @Vesta.ScalarField @Pallas.ScalarField
  let endoVar = const_ endoCoeff
  toField challenge endoVar

-- Generator for 128-bit scalar challenges
genScalarChallenge :: Gen TestInput
genScalarChallenge = do
  -- Generate a 128-bit scalar challenge (following OCaml pattern)
  bits128 <- Gen.vectorOf 128 arbitrary
  let
    scalar = foldl (\acc bit -> acc + acc + if bit then one else zero) zero bits128
  pure $ F scalar

-- Test specification
spec :: Spec Unit
spec = do
  describe "EndoScale" do
    it "EndoScale Circuit correctly decomposes and reconstructs scalar challenges" $
      let
        f :: TestInput -> TestInput
        f = refEndoScale

        solver = makeSolver (Proxy @(KimchiConstraint Vesta.ScalarField)) circuit

        { constraints } = compilePure
          (Proxy @TestInput)
          (Proxy @TestInput)
          (Proxy @(KimchiConstraint Vesta.ScalarField))
          circuit
          Kimchi.initialState
      in
        circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) genScalarChallenge