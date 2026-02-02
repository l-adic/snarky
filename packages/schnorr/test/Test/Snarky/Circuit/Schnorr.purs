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
import Poseidon as Poseidon
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, BoolVar, FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Schnorr (SignatureVar(..), pallasScalarOps, verifies)
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (fromAffine, generator, inverse, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Types.Shifted (fromShifted, splitField)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | Circuit specification for Schnorr verification
-- | Specialized for Pallas.BaseField (= Vesta.ScalarField) since Type2 only has
-- | a CheckedType instance for this specific field.
verifySpec
  :: forall k
   . Reflectable k Int
  => Proxy k
  -> Aff Unit
verifySpec _pk = do
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

    -- | Pure reference function for verification.
    -- | This must match what the circuit computes, including the shift transformation
    -- | used by scaleFast2 for scalar multiplication.
    -- | Pallas.BaseField = base field of curve Pallas.G (circuit field)
    -- | Pallas.ScalarField = scalar field of curve Pallas.G
    testFunction :: VerifyInput k (F Pallas.BaseField) Boolean -> Boolean
    testFunction { signature: { r: F r, s: sigS }, publicKey: pk, message } =
      let
        publicKey = { x: case pk.x of F x -> x, y: case pk.y of F y -> y }

        s = case fromShifted sigS of F x -> x

        -- e is a circuit field hash, split to Type2 and get effective scalar via Shifted
        e :: Pallas.ScalarField
        e =
          let
            eBase = Poseidon.hash $ publicKey.x : publicKey.y : r : (un F <$> Vector.toUnfoldable message)
          in
            case fromShifted (splitField (F eBase)) of F x -> x

        pkPoint = fromAffine @Pallas.BaseField @Pallas.G publicKey
        sG = scalarMul s generator
        ePk = scalarMul e pkPoint
        rPoint = sG <> inverse ePk
      in
        case toAffine rPoint of
          Nothing -> false
          Just { x: rx, y: ry } -> Schnorr.isEven ry && rx == r

    circuit
      :: forall t
       . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
      => VerifyInput k (FVar Pallas.BaseField) (BoolVar Pallas.BaseField)
      -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (BoolVar Pallas.BaseField)
    circuit { signature: { r: sigR, s: sigS }, publicKey, message } =
      let
        signature = SignatureVar { r: sigR, s: sigS }
      in
        verifies (pallasScalarOps @51) genPointVar { signature, publicKey, message }

    solver = makeSolver (Proxy @(KimchiConstraint Pallas.BaseField)) circuit
    st = compilePure
      (Proxy @(VerifyInput k (F Pallas.BaseField) Boolean))
      (Proxy @Boolean)
      (Proxy @(KimchiConstraint Pallas.BaseField))
      circuit
      Kimchi.initialState

    gen = genValidSignature (Proxy @Pallas.G) _pk

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
-- | Uses Pallas curve where we need scaleFast2 for foreign field scalar multiplication.
-- | Type2 is used when scalar field > circuit field (Pallas.ScalarField > Pallas.BaseField).
spec :: Spec Unit
spec = describe "Snarky.Circuit.Schnorr" do
  describe "verifies" do
    it "Pallas curve verification circuit matches pure implementation" do
      verifySpec (Proxy @5)
