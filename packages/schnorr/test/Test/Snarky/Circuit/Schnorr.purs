module Test.Snarky.Circuit.Schnorr
  ( spec
  ) where

import Prelude

import Data.Array ((:))
import Data.Generic.Rep (class Generic)
import Data.Identity (Identity)
import Data.Maybe (Maybe(..), fromJust, isJust)
import Data.Newtype (class Newtype, un)
import Data.Reflectable (class Reflectable)
import Data.Schnorr (safeFieldCoerce)
import Data.Schnorr as Schnorr
import Data.Vector (Vector)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import JS.BigInt (fromInt, shl)
import Partial.Unsafe (unsafePartial)
import Poseidon (class PoseidonField)
import Poseidon as Poseidon
import Prim.Int (class Add)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Schnorr (SignatureVar(..), verifies)
import Snarky.Circuit.Types (class CircuitType, F(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class PrimeField, class WeierstrassCurve, fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | Input type for Schnorr verification circuit
-- | All values are in the circuit field f (base field of curve g)
newtype VerifyInput n a = VerifyInput
  { sigR :: a
  , sigS :: a
  , publicKey :: AffinePoint a
  , message :: Vector n a
  }

derive instance Newtype (VerifyInput n a) _
derive instance Generic (VerifyInput n a) _

instance Reflectable n Int => CircuitType f (VerifyInput n (F f)) (VerifyInput n (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(VerifyInput n (F f))
  fieldsToVar = genericFieldsToVar @(VerifyInput n (F f))

--------------------------------------------------------------------------------
-- | Convert between fields via bit representation (preserves integer value)
coerceViaBits :: forall f f'. PrimeField f => PrimeField f' => FieldSizeInBits f 255 => FieldSizeInBits f' 255 => f -> f'
coerceViaBits = packPure <<< unpackPure

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
-- | Generate a valid signature for testing using the library's sign function.
-- | Returns VerifyInput with all values in the circuit field (base field).
-- | f = base field of curve g (circuit field)
-- | f' = scalar field of curve g
genValidSignature
  :: forall f f' g n
   . PoseidonField f
  => PrimeField f'
  => Reflectable n Int
  => WeierstrassCurve f g
  => FrModule f' g
  => PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Proxy g
  -> Proxy n
  -> Gen (VerifyInput n (F f))
genValidSignature pg pn = do
  -- Generate random private key (in scalar field f')
  privateKey <- arbitrary @f' `suchThat` \sk ->
    isJust $ toAffine $ scalarMul sk (generator @_ @g)
  let
    publicKey = unsafePartial fromJust
      $ toAffine
      $ scalarMul privateKey (generator @_ @g)
  -- Generate random message field element (in base field f)
  message <- Vector.generateA @n (const arbitrary)

  -- Compute public key first (this ties the curve type g)

  let
    kPrimeBase = Poseidon.hash $ publicKey.x : publicKey.y : Vector.toUnfoldable message

    kPrime :: f'
    kPrime = safeFieldCoerce kPrimeBase

  if kPrime == zero then
    genValidSignature pg pn
  else
    case toAffine $ scalarMul kPrime (generator @_ @g) of
      Nothing -> genValidSignature pg pn
      Just { x: r, y: ry } -> do
        let
          k = if Schnorr.isEven ry then kPrime else negate kPrime
          eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : Vector.toUnfoldable message

          e :: f'
          e = fromBigInt (toBigInt eBase)

          s :: f'
          s = k + e * privateKey

          -- Convert s from scalar field to base field via bits
          sInBaseField :: f
          sInBaseField = coerceViaBits s

        pure $ VerifyInput
          { sigR: F r
          , sigS: F sInBaseField
          , publicKey: { x: F publicKey.x, y: F publicKey.y }
          , message: map F message
          }

--------------------------------------------------------------------------------
-- | Circuit specification for Schnorr verification
verifySpec
  :: forall f f' g g' k l
   . KimchiVerify f f'
  => Reflectable k Int
  => Add 3 k l
  => Reflectable l Int
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
verifySpec _ pg pn = do
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
    testFunction (VerifyInput { sigR: F r, sigS: F sInBaseField, publicKey: pk, message }) =
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
    circuit (VerifyInput { sigR, sigS, publicKey, message }) =
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

    gen = genValidSignature pg pn

  circuitSpecPure'
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
