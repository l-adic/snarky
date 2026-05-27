module Test.Snarky.Circuit.Schnorr
  ( spec
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Data.Schnorr as Schnorr
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, assert_, const_)
import Snarky.Circuit.Kimchi (verifyCircuit)
import Snarky.Circuit.Schnorr (Signature(..), verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (generator, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (PallasG)
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied, satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- | Pallas-curve verification circuit roundtrip:
-- | `Data.Schnorr.sign` should always produce a signature accepted by
-- | `Snarky.Circuit.Schnorr.verifies`. The reference verifier
-- | (`Data.Schnorr.verify`) mirrors the circuit math.
verifySpec
  :: forall n
   . Reflectable n Int
  => TestConfig Pallas.BaseField (KimchiGate Pallas.BaseField) (AuxState Pallas.BaseField)
  -> Proxy n
  -> Aff Unit
verifySpec cfg _pn = do
  let
    genPointVar :: AffinePoint (FVar Pallas.BaseField)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator :: PallasG)
      in
        { x: const_ x, y: const_ y }

    testFunction :: VerifyInput n (F Pallas.BaseField) -> Boolean
    testFunction { signature: { r: F r, s: F s }, publicKey: pk, message } =
      let
        publicKey = { x: un F pk.x, y: un F pk.y }
        msgArr = un F <$> Vector.toUnfoldable message
      in
        Schnorr.verify (Schnorr.Signature { r, s }) publicKey msgArr

    circuit'
      :: forall t
       . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
      => VerifyInput n (FVar Pallas.BaseField)
      -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (BoolVar Pallas.BaseField)
    circuit' { signature: { r, s }, publicKey, message } =
      verifies genPointVar { publicKey, signature: Signature { r, s }, message }

    gen = genValidSignature (Proxy @PallasG) _pn

  { builtState, solver } <- circuitTest' @Pallas.BaseField
    cfg
    (NEA.singleton { testFunction: satisfied testFunction, input: QuickCheck 10 gen })
    circuit'
  liftEffect $ verifyCircuit { s: builtState, gen, solver }

-- | Variant that asserts the verifier accepts inside the circuit
-- | (no boolean return).
verifyWithAssertSpec
  :: forall n
   . Reflectable n Int
  => TestConfig Pallas.BaseField (KimchiGate Pallas.BaseField) (AuxState Pallas.BaseField)
  -> Proxy n
  -> Aff Unit
verifyWithAssertSpec cfg _pn = do
  let
    genPointVar :: AffinePoint (FVar Pallas.BaseField)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator :: PallasG)
      in
        { x: const_ x, y: const_ y }

    circuit'
      :: forall t
       . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
      => VerifyInput n (FVar Pallas.BaseField)
      -> Snarky (KimchiConstraint Pallas.BaseField) t Identity Unit
    circuit' { signature: { r, s }, publicKey, message } = do
      verified <- verifies genPointVar { publicKey, signature: Signature { r, s }, message }
      assert_ verified

    gen = genValidSignature (Proxy @PallasG) _pn

  void $ circuitTest' @Pallas.BaseField
    cfg
    (NEA.singleton { testFunction: satisfied_, input: QuickCheck 10 gen })
    circuit'

spec
  :: TestConfig Pallas.BaseField (KimchiGate Pallas.BaseField) (AuxState Pallas.BaseField)
  -> Spec Unit
spec cfg = describe "Snarky.Circuit.Schnorr" do
  describe "verifies" do
    it "Pallas curve verification circuit matches pure implementation" do
      verifySpec cfg (Proxy @1)
    it "Pallas curve verification with assert_ inside circuit" do
      verifyWithAssertSpec cfg (Proxy @1)
