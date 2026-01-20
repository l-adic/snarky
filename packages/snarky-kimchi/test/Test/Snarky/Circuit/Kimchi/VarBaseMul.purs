module Test.Snarky.Circuit.Kimchi.VarBaseMul where

import Prelude

import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import JS.BigInt (fromInt, shl)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky)
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1, scaleFast2)
import Snarky.Circuit.Types (F, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class PrimeField, fromAffine, fromBigInt, scalarMul, toAffine, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Snarky.Types.Shifted (class Shifted, Type1(..))
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  describe "VarBaseMul Type1" do
    it "varBaseMul Circuit is Valid for Type1" $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F Pallas.BaseField)) (Type1 (F Pallas.BaseField)) -> AffinePoint (F Pallas.BaseField)
        f (Tuple { x: F x, y: F y } (Type1 (F t))) =
          let
            base = fromAffine { x, y }
            result = scalarMul (fieldShift1 t) base
            { x, y } = unsafePartial $ fromJust $ toAffine @Pallas.BaseField @Pallas.G result
          in
            { x: F x, y: F y }
        solver = makeSolver (Proxy @(KimchiConstraint Pallas.BaseField)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
          => AffinePoint (FVar Pallas.BaseField)
          -> Type1 (FVar Pallas.BaseField)
          -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (AffinePoint (FVar Pallas.BaseField))
        circuit p t = do
          g <- scaleFast1 @51 p t
          pure g
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F Pallas.BaseField)) (Type1 (F Pallas.BaseField))))
            (Proxy @(AffinePoint (F Pallas.BaseField)))
            (Proxy @(KimchiConstraint Pallas.BaseField))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Shifted Type1 Pallas.BaseField => Gen (Tuple (AffinePoint (F Pallas.BaseField)) (Type1 (F Pallas.BaseField)))
        gen = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          t <- arbitrary
          pure $ Tuple p (Type1 t)
      in
        do
          circuitSpecPure' 100
            { builtState: s
            , checker: Kimchi.eval
            , solver: solver
            , testFunction: satisfied f
            , postCondition: Kimchi.postCondition
            }
            gen
          liftEffect $ verifyCircuit { s, gen, solver }

  describe "VarBaseMul Type2" do
    it "varBaseMul Circuit is Valid for Type2" $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F Vesta.BaseField)) (F Vesta.BaseField) -> AffinePoint (F Vesta.BaseField)
        f = uncurry \{ x: F x, y: F y } (F t) ->
          let
            base = fromAffine @Vesta.BaseField @Vesta.G { x, y }
            result = scalarMul (fieldShift2 t) base
            { x, y } = unsafePartial $ fromJust $ toAffine @Vesta.BaseField result
          in
            { x: F x, y: F y }
        solver = makeSolver (Proxy @(KimchiConstraint Vesta.BaseField)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM Vesta.BaseField (KimchiConstraint Vesta.BaseField) t Identity
          => AffinePoint (FVar Vesta.BaseField)
          -> FVar Vesta.BaseField
          -> Snarky (KimchiConstraint Vesta.BaseField) t Identity (AffinePoint (FVar Vesta.BaseField))
        circuit p t = do
          g <- scaleFast2 @51 p t
          pure g
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F Vesta.BaseField)) (F Vesta.BaseField)))
            (Proxy @(AffinePoint (F Vesta.BaseField)))
            (Proxy @(KimchiConstraint Vesta.BaseField))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Gen (Tuple (AffinePoint (F Vesta.BaseField)) (F Vesta.BaseField))
        gen = do
          p <- EC.genAffinePoint (Proxy @Vesta.G)
          t <- arbitrary
          pure $ Tuple p t
      in
        do
          circuitSpecPure' 100
            { builtState: s
            , checker: Kimchi.eval
            , solver: solver
            , testFunction: satisfied f
            , postCondition: Kimchi.postCondition
            }
            gen
          liftEffect $ verifyCircuit { s, gen, solver }

-- | Shift field element for Type1 scalar multiplication
-- | Result: 2*t + 1 + 2^255 (ensures high bit is set for constant-time scalar mul)
fieldShift1 :: forall f f' n. FieldSizeInBits f n => FieldSizeInBits f' n => PrimeField f' => f -> f'
fieldShift1 t =
  let
    coerceViaBits :: f -> f'
    coerceViaBits = packPure <<< unpackPure
    two = one + one
    twoToThe255 = fromBigInt $ toBigInt (one :: Vesta.BaseField) `shl` fromInt 255
  in
    (two * coerceViaBits t) + one + twoToThe255

-- | Shift field element for Type2 scalar multiplication
-- | Result: t + 2^255 (ensures high bit is set for constant-time scalar mul)
fieldShift2 :: forall f f' n. FieldSizeInBits f n => FieldSizeInBits f' n => PrimeField f' => f -> f'
fieldShift2 t =
  let
    coerceViaBits :: f -> f'
    coerceViaBits = packPure <<< unpackPure
    twoToThe255 = fromBigInt $ toBigInt (one :: Pallas.BaseField) `shl` fromInt 255
  in
    coerceViaBits t + twoToThe255
