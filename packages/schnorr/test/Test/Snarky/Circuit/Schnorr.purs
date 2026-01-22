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
import Data.Schnorr.Gen (VerifyInput, coerceViaBits, genValidSignature)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt (fromInt, shl)
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
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class PrimeField, class WeierstrassCurve, fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | Apply the shift transformation used by scaleFast2 in the circuit.
-- | When the circuit computes [s]*G using scaleFast2, it internally shifts the value.
-- | The pure scalarMul needs the same shift to produce matching results.
fieldShift2 :: forall f f'. FieldSizeInBits f 255 => FieldSizeInBits f' 255 => PrimeField f' => f -> f'
fieldShift2 t =
  let
    twoToThe255 = fromBigInt $ one `shl` fromInt 255
  in
    coerceViaBits t + twoToThe255

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
    testFunction :: VerifyInput k (F f) -> Boolean
    testFunction { signature: { r: F r, s: F sInBaseField }, publicKey: pk, message } =
      let
        publicKey = { x: case pk.x of F x -> x, y: case pk.y of F y -> y }

        -- Apply fieldShift2 to match scaleFast2's internal transformation
        -- The circuit uses scaleFast2 which shifts the scalar by 2^255
        s :: f'
        s = fieldShift2 sInBaseField

        -- Compute e = H(pk_x, pk_y, r, msgHash)
        eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : (un F <$> Vector.toUnfoldable message)

        -- Apply fieldShift2 to e as well (circuit uses scaleFast2 for e*pk too)
        e :: f'
        e = fieldShift2 eBase

        -- Compute R' = s*G - e*pk (using shifted values for scalarMul)
        pkPoint = fromAffine @f @g publicKey
        sG = scalarMul s generator
        ePk = scalarMul e pkPoint
        rPoint = sG <> inverse ePk
      in
        case toAffine rPoint of
          Nothing -> false
          Just { x: rx, y: ry } -> Schnorr.isEven ry && rx == r

    -- Circuit function
    circuit
      :: forall t
       . CircuitM f (KimchiConstraint f) t Identity
      => VerifyInput k (FVar f)
      -> Snarky (KimchiConstraint f) t Identity (BoolVar f)
    circuit { signature: { r: sigR, s: sigS }, publicKey, message } =
      let
        sig = SignatureVar { r: sigR, s: sigS }
      in
        verifies @51 genPointVar sig publicKey message

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    st = compilePure
      (Proxy @(VerifyInput k (F f)))
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
-- | For Pallas curve: base field = VestaScalarField, scalar field = PallasScalarField
-- | For Vesta curve: base field = PallasScalarField, scalar field = VestaScalarField
spec :: Spec Unit
spec = describe "Snarky.Circuit.Schnorr" do
  describe "verifies" do
    it "Pallas curve verification circuit matches pure implementation" do
      verifySpec (Proxy @Vesta.ScalarField) (Proxy @Pallas.G) (Proxy @4)

    it "Vesta curve verification circuit matches pure implementation" do
      verifySpec (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) (Proxy @5)
