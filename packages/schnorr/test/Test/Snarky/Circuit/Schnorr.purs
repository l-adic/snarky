module Test.Snarky.Circuit.Schnorr
  ( spec
  ) where

import Prelude

import Data.Identity (Identity)
import Data.Maybe (Maybe(..), fromJust)
import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Schnorr as Schnorr
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
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Circuit.Schnorr (SignatureVar(..), verifies)
import Snarky.Circuit.Types (F(..), class CircuitType, genericValueToFields, genericFieldsToValue, genericSizeInFields, genericVarToFields, genericFieldsToVar)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class Generator, class PrimeField, class WeierstrassCurve, fromAffine, fromBigInt, generator, inverse, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | Input type for Schnorr verification circuit
-- | All values are in the circuit field f (base field of curve g)
newtype VerifyInput a = VerifyInput
  { sigR :: a
  , sigS :: a
  , publicKey :: AffinePoint a
  , msgDigest :: Digest a
  }

derive instance Newtype (VerifyInput a) _
derive instance Generic (VerifyInput a) _

instance CircuitType f (VerifyInput (F f)) (VerifyInput (FVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(VerifyInput (F f))
  fieldsToVar = genericFieldsToVar @(VerifyInput (F f))

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
  :: forall f f' g
   . PoseidonField f
  => PrimeField f'
  => WeierstrassCurve f g
  => FrModule f' g
  => Generator g
  => PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Proxy g
  -> Gen (VerifyInput (F f))
genValidSignature _ = do
  -- Generate random private key (in scalar field f')
  privateKey <- arbitrary @f'
  -- Generate random message field element (in base field f)
  msgField <- arbitrary @f

  -- Compute public key first (this ties the curve type g)
  let
    gen :: g
    gen = generator
    pkPoint = scalarMul privateKey gen

  case toAffine pkPoint of
    Nothing -> genValidSignature (Proxy @g) -- Retry if point at infinity
    Just publicKey -> do
      -- Derive nonce deterministically
      let
        msgHash = Poseidon.hash [ msgField ]
        kPrimeBase = Poseidon.hash [ publicKey.x, publicKey.y, msgHash ]
        kPrime :: f'
        kPrime = fromBigInt (toBigInt kPrimeBase)

      if kPrime == zero then
        genValidSignature (Proxy @g)
      else
        case toAffine $ scalarMul kPrime gen of
          Nothing -> genValidSignature (Proxy @g)
          Just { x: r, y: ry } -> do
            let
              k = if Schnorr.isEven ry then kPrime else negate kPrime
              eBase = Poseidon.hash [ publicKey.x, publicKey.y, r, msgHash ]
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
              , msgDigest: Digest $ F $ Poseidon.hash [ msgField ]
              }

--------------------------------------------------------------------------------
-- | Pure reference function for verification.
-- | This must match what the circuit computes, including the shift transformation
-- | used by scaleFast2 for scalar multiplication.
-- | f = base field of curve g (circuit field)
-- | f' = scalar field of curve g
pureVerify
  :: forall f f' g
   . PoseidonField f
  => PrimeField f'
  => WeierstrassCurve f g
  => FrModule f' g
  => Generator g
  => PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Proxy g
  -> VerifyInput (F f)
  -> Boolean
pureVerify _ (VerifyInput { sigR: F r, sigS: F sInBaseField, publicKey: pk, msgDigest: Digest (F msgHash) }) =
  let
    publicKey = { x: case pk.x of F x -> x, y: case pk.y of F y -> y }

    -- Apply fieldShift2 to match scaleFast2's internal transformation
    -- The circuit uses scaleFast2 which shifts the scalar by 2^255
    s :: f'
    s = fieldShift2 sInBaseField

    -- Compute e = H(pk_x, pk_y, r, msgHash)
    eBase = Poseidon.hash [ publicKey.x, publicKey.y, r, msgHash ]
    -- Apply fieldShift2 to e as well (circuit uses scaleFast2 for e*pk too)
    e :: f'
    e = fieldShift2 eBase

    -- Compute R' = s*G - e*pk (using shifted values for scalarMul)
    pkPoint = fromAffine @f @g publicKey
    sG = scalarMul s (generator @g)
    ePk = scalarMul e pkPoint
    rPoint = sG <> inverse ePk
  in
    case toAffine rPoint of
      Nothing -> false
      Just { x: rx, y: ry } -> Schnorr.isEven ry && rx == r

--------------------------------------------------------------------------------
-- | Circuit specification for Schnorr verification
verifySpec
  :: forall f f' g g'
   . KimchiVerify f f'
  => CircuitGateConstructor f g'
  => PoseidonField f
  => WeierstrassCurve f g
  => FrModule f' g
  => Generator g
  => PrimeField f
  => PrimeField f'
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Proxy f
  -> Proxy g
  -> Aff Unit
verifySpec _ pg = do
  let
    -- Generator point (get the raw field coordinates)
    genPointRaw :: AffinePoint f
    genPointRaw = unsafePartial fromJust $ toAffine (generator @g)

    -- Generator as circuit constants
    genPointVar :: AffinePoint (FVar f)
    genPointVar = { x: const_ genPointRaw.x
                  , y: const_ genPointRaw.y
                  }

    -- Pure test function
    testFunction :: VerifyInput (F f) -> Boolean
    testFunction = pureVerify pg

    -- Circuit function
    circuit
      :: forall t
       . CircuitM f (KimchiConstraint f) t Identity
      => VerifyInput (FVar f)
      -> Snarky (KimchiConstraint f) t Identity (BoolVar f)
    circuit (VerifyInput { sigR, sigS, publicKey, msgDigest }) =
      let
        sig = SignatureVar { r: sigR, s: sigS }
      in
        verifies @51 genPointVar sig publicKey msgDigest

    solver = makeSolver (Proxy @(KimchiConstraint f)) circuit
    s = compilePure
      (Proxy @(VerifyInput (F f)))
      (Proxy @Boolean)
      (Proxy @(KimchiConstraint f))
      circuit
      Kimchi.initialState

    gen = genValidSignature pg

  circuitSpecPure'
    { builtState: s
    , checker: Kimchi.eval
    , solver: solver
    , testFunction: satisfied testFunction
    , postCondition: Kimchi.postCondition
    }
    gen

  liftEffect $ verifyCircuit { s, gen, solver }

--------------------------------------------------------------------------------
-- | Test spec
-- | For Pallas curve: base field = VestaScalarField, scalar field = PallasScalarField
-- | For Vesta curve: base field = PallasScalarField, scalar field = VestaScalarField
spec :: Spec Unit
spec = describe "Snarky.Circuit.Schnorr" do
  describe "verifies" do
    it "Pallas curve verification circuit matches pure implementation" do
      verifySpec (Proxy @Vesta.ScalarField) (Proxy @Pallas.G)

    it "Vesta curve verification circuit matches pure implementation" do
      verifySpec (Proxy @Pallas.ScalarField) (Proxy @Vesta.G)
