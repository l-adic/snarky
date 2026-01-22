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
import Data.Schnorr (truncateFieldCoerce)
import Data.Schnorr as Schnorr
import Data.Vector (Vector)
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
import Snarky.Circuit.Types (class CircuitType, F(..), genericFieldsToValue, genericFieldsToVar, genericSizeInFields, genericValueToFields, genericVarToFields)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class PrimeField, class WeierstrassCurve, fromAffine, generator, inverse, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (class Shifted, Type2, fromShifted, splitField, toShifted)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | Input type for Schnorr verification circuit
-- | sigR is the x-coordinate of R (circuit field element)
-- | sigS is the signature s component as Type2 (scalar field element in circuit representation)
-- | publicKey and message are in the circuit field
newtype VerifyInput n a b = VerifyInput
  { sigR :: a
  , sigS :: Type2 a b
  , publicKey :: AffinePoint a
  , message :: Vector n a
  }

derive instance Newtype (VerifyInput n a b) _
derive instance Generic (VerifyInput n a b) _

instance (Reflectable n Int, PrimeField f) => CircuitType f (VerifyInput n (F f) Boolean) (VerifyInput n (FVar f) (BoolVar f)) where
  valueToFields = genericValueToFields
  fieldsToValue = genericFieldsToValue
  sizeInFields = genericSizeInFields
  varToFields = genericVarToFields @(VerifyInput n (F f) Boolean)
  fieldsToVar = genericFieldsToVar @(VerifyInput n (F f) Boolean)

--------------------------------------------------------------------------------
-- | Generate a valid signature for testing using the library's sign function.
-- | Returns VerifyInput with sigS as Type2 (proper scalar field representation).
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
  => Shifted (F f') (Type2 (F f) Boolean)
  => Proxy g
  -> Proxy n
  -> Gen (VerifyInput n (F f) Boolean)
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
    kPrime = truncateFieldCoerce kPrimeBase

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
          e = truncateFieldCoerce eBase

          s :: f'
          s = k + e * privateKey

          -- Convert s to Type2 representation using toShifted
          sigS :: Type2 (F f) Boolean
          sigS = toShifted (F s)

        pure $ VerifyInput
          { sigR: F r
          , sigS
          , publicKey: { x: F publicKey.x, y: F publicKey.y }
          , message: map F message
          }

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
    testFunction (VerifyInput { sigR: F r, sigS, publicKey: pk, message }) =
      let
        publicKey = { x: case pk.x of F x -> x, y: case pk.y of F y -> y }

        -- Get effective scalar from Type2 using fromShifted
        s :: f'
        s = case fromShifted sigS of F x -> x

        -- Compute e = H(pk_x, pk_y, r, msgHash)
        eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : (un F <$> Vector.toUnfoldable message)

        -- e is a circuit field hash, split to Type2 and get effective scalar via Shifted
        -- This mirrors what the circuit does with splitFieldVar
        e :: f'
        e = case fromShifted (splitField (F eBase)) of F x -> x

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
      => VerifyInput k (FVar f) (BoolVar f)
      -> Snarky (KimchiConstraint f) t Identity (BoolVar f)
    circuit (VerifyInput { sigR, sigS, publicKey, message }) =
      let
        sig = SignatureVar { r: sigR, s: sigS }
      in
        verifies @51 genPointVar sig publicKey message

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
