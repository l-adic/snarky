module Test.Snarky.Circuit.Schnorr
  ( spec
  ) where

import Prelude

import Data.Array ((:))
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Data.Schnorr as Schnorr
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt as BigInt
import Partial.Unsafe (unsafePartial)
import Poseidon as Poseidon
import Snarky.Circuit.DSL (class CircuitM, BoolVar, F(..), FVar, Snarky, assert_, const_)
import Snarky.Circuit.Kimchi (fieldSizeBits, verifyCircuit)
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Constraint.Kimchi (KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied, satisfied_)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | Circuit specification for Schnorr verification
-- | Specialized for Pallas.BaseField (= Vesta.ScalarField).
-- | Uses scaleFast2' which handles the parity split + 2^n shift internally.
verifySpec
  :: forall k
   . Reflectable k Int
  => TestConfig Pallas.BaseField (KimchiGate Pallas.BaseField) (AuxState Pallas.BaseField)
  -> Proxy k
  -> Aff Unit
verifySpec cfg _pk = do
  let
    -- Generator as circuit constants
    genPointVar :: AffinePoint (FVar Pallas.BaseField)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator @_ @Pallas.G)
      in
        { x: const_ x
        , y: const_ y
        }

    -- 2^n in the scalar field (for computing effective scalars)
    twoToN :: Pallas.ScalarField
    twoToN =
      let
        n = fieldSizeBits (Proxy @Pallas.BaseField)
      in
        fromBigInt $ BigInt.pow (BigInt.fromInt 2) (BigInt.fromInt n)

    -- | Pure reference function for verification.
    -- | The circuit uses scaleFast2' which computes [value + 2^n] * base,
    -- | so the effective scalars are (s + 2^n) and (e + 2^n).
    testFunction :: VerifyInput k (F Pallas.BaseField) -> Boolean
    testFunction { signature: { r: F r, s: F sigS }, publicKey: pk, message } =
      let
        publicKey = { x: case pk.x of F x -> x, y: case pk.y of F y -> y }

        -- Effective scalar: sigS (base field) reinterpreted in scalar field + 2^n
        s :: Pallas.ScalarField
        s = fromBigInt (toBigInt sigS) + twoToN

        -- e is a circuit field hash; effective scalar: eBase + 2^n
        e :: Pallas.ScalarField
        e =
          let
            eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : (un F <$> Vector.toUnfoldable message)
          in
            fromBigInt (toBigInt eBase) + twoToN

        pkPoint = fromAffine @Pallas.BaseField @Pallas.G publicKey
        sG = scalarMul s generator
        ePk = scalarMul e pkPoint
        rPoint = sG <> inverse ePk
      in
        case toAffine rPoint of
          Nothing -> false
          Just { x: rx, y: ry } -> Schnorr.isEven ry && rx == r

    circuit'
      :: forall t
       . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
      => VerifyInput k (FVar Pallas.BaseField)
      -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (BoolVar Pallas.BaseField)
    circuit' { signature: { r: sigR, s: sigS }, publicKey, message } =
      let
        signature = SignatureVar { r: sigR, s: sigS }
      in
        verifies (pallasScalarOps @51) genPointVar { signature, publicKey, message }

    gen = genValidSignature (Proxy @Pallas.G) _pk

  { builtState, solver } <- circuitTest' @Pallas.BaseField
    cfg
    (NEA.singleton { testFunction: satisfied testFunction, input: QuickCheck 100 gen })
    circuit'
  liftEffect $ verifyCircuit { s: builtState, gen, solver }

--------------------------------------------------------------------------------
-- | Test that uses assert_ inside the circuit instead of returning the result
verifyWithAssertSpec
  :: forall k
   . Reflectable k Int
  => TestConfig Pallas.BaseField (KimchiGate Pallas.BaseField) (AuxState Pallas.BaseField)
  -> Proxy k
  -> Aff Unit
verifyWithAssertSpec cfg _pk = do
  let
    genPointVar :: AffinePoint (FVar Pallas.BaseField)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator @_ @Pallas.G)
      in
        { x: const_ x, y: const_ y }

    circuit'
      :: forall t
       . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
      => VerifyInput k (FVar Pallas.BaseField)
      -> Snarky (KimchiConstraint Pallas.BaseField) t Identity Unit
    circuit' { signature: { r: sigR, s: sigS }, publicKey, message } = do
      let signature = SignatureVar { r: sigR, s: sigS }
      verified <- verifies (pallasScalarOps @51) genPointVar { signature, publicKey, message }
      assert_ verified

    gen = genValidSignature (Proxy @Pallas.G) _pk

  void $ circuitTest' @Pallas.BaseField
    cfg
    (NEA.singleton { testFunction: satisfied_, input: QuickCheck 100 gen })
    circuit'

spec
  :: TestConfig Pallas.BaseField (KimchiGate Pallas.BaseField) (AuxState Pallas.BaseField)
  -> Spec Unit
spec cfg = describe "Snarky.Circuit.Schnorr" do
  describe "verifies" do
    it "Pallas curve verification circuit matches pure implementation" do
      verifySpec cfg (Proxy @5)
    it "Pallas curve verification with assert_ inside circuit" do
      verifyWithAssertSpec cfg (Proxy @5)
