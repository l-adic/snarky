module Test.Snarky.Circuit.Schnorr
  ( spec
  ) where

import Prelude

import Data.Array ((:))
import Data.Identity (Identity)
import Data.Maybe (Maybe(..), fromJust)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Data.Schnorr as Schnorr
import Data.Schnorr.Gen (VerifyInput, genValidSignature)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Schnorr (SignatureVar(..), verifies)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class PrimeField, class WeierstrassCurve, fromAffine, generator, inverse, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (class Shifted, Type2, fromShifted, splitField)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | Circuit specification for Schnorr verification
verifySpec
  :: forall f f' g g' k
   . KimchiVerify f f'
  => Reflectable k Int
  => CircuitGateConstructor f g'
  => PoseidonField f
  => WeierstrassCurve f g
  => FrModule f' g
  => PrimeField f
  => PrimeField f'
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Shifted (F f') (Type2 (F f) Boolean)
  => Proxy f
  -> Proxy g
  -> Proxy k
  -> Aff Unit
verifySpec _ pg _pk = do
  let
    -- Generator as circuit constants
    genPointVar :: AffinePoint (FVar f)
    genPointVar =
      let
        { x, y } = unsafePartial fromJust $ toAffine (generator @_ @g)
      in
        { x: const_ x
        , y: const_ y
        }

    -- | Pure reference function for verification.
    -- | This must match what the circuit computes, including the shift transformation
    -- | used by scaleFast2 for scalar multiplication.
    -- | f = base field of curve g (circuit field)
    -- | f' = scalar field of curve g
    testFunction :: VerifyInput k (F f) Boolean -> Boolean
    testFunction { signature: { r: F r, s: sigS }, publicKey: pk, message } =
      let
        publicKey = { x: case pk.x of F x -> x, y: case pk.y of F y -> y }

        s = case fromShifted sigS of F x -> x

        -- e is a circuit field hash, split to Type2 and get effective scalar via Shifted
        e :: f'
        e =
          let
            eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : (un F <$> Vector.toUnfoldable message)
          in
            case fromShifted (splitField (F eBase)) of F x -> x

        pkPoint = fromAffine @f @g publicKey
        sG = scalarMul s generator
        ePk = scalarMul e pkPoint
        rPoint = sG <> inverse ePk
      in
        case toAffine rPoint of
          Nothing -> false
          Just { x: rx, y: ry } -> Schnorr.isEven ry && rx == r

    circuit
      :: forall t
       . CircuitM f (KimchiConstraint f) t Identity
      => VerifyInput k (FVar f) (BoolVar f)
      -> Snarky (KimchiConstraint f) t Identity (BoolVar f)
    circuit { signature: { r: sigR, s: sigS }, publicKey, message } =
      let
        signature = SignatureVar { r: sigR, s: sigS }
      in
        verifies @51 genPointVar { signature, publicKey, message }

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    st = compilePure
      (Proxy @(VerifyInput k (F f) Boolean))
      (Proxy @Boolean)
      (Proxy @(KimchiConstraint f))
      circuit
      Kimchi.initialState

    gen = genValidSignature pg _pk

  circuitSpecPure' 100
    { builtState: st
    , checker: Kimchi.eval
    , solver: solver
    , testFunction: satisfied testFunction
    , postCondition: Kimchi.postCondition
    }
    gen
  liftEffect $ verifyCircuit { s: st, gen, solver }

--------------------------------------------------------------------------------
-- | Test spec
-- | Uses Vesta curve where scalar field (Pallas.BaseField) > circuit field (Vesta.BaseField)
-- | This is the foreign field case that scaleFast2 is designed for.
spec :: Spec Unit
spec = describe "Snarky.Circuit.Schnorr" do
  describe "verifies" do
    it "Vesta curve verification circuit matches pure implementation" do
      verifySpec (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) (Proxy @5)
