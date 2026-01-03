module Test.Snarky.Circuit.Kimchi.VarBaseMul where

import Prelude

import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import JS.BigInt (fromInt, shl)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky)
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1, scaleFast2)
import Snarky.Circuit.Types (F, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
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

type Fq = Vesta.ScalarField
type Fp = Pallas.ScalarField

spec :: Spec Unit
spec = do
  describe "VarBaseMul Type1" do
    it "varBaseMul Circuit is Valid for Type1" $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F Fq)) (Type1 (F Fq)) -> AffinePoint (F Fq)
        f (Tuple { x: F x, y: F y } (Type1 (F t))) =
          let
            base = fromAffine { x, y }
            result = scalarMul (fieldShift1 t) base
            { x, y } = unsafePartial $ fromJust $ toAffine @Fq @Pallas.G result
          in
            { x: F x, y: F y }
        solver = makeSolver (Proxy @(KimchiConstraint Fq)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM Fq (KimchiConstraint Fq) t Identity
          => AffinePoint (FVar Fq)
          -> Type1 (FVar Fq)
          -> Snarky (KimchiConstraint Fq) t Identity (AffinePoint (FVar Fq))
        circuit p t = do
          g <- scaleFast1 @51 p t
          pure g
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F Fq)) (Type1 (F Fq))))
            (Proxy @(AffinePoint (F Fq)))
            (Proxy @(KimchiConstraint Fq))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Shifted Type1 Fq => Gen (Tuple (AffinePoint (F Fq)) (Type1 (F Fq)))
        gen = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          t <- arbitrary
          pure $ Tuple p (Type1 t)
      in
        do
          circuitSpecPure' s KimchiConstraint.eval solver (satisfied f) gen Kimchi.postCondition

  describe "VarBaseMul Type2" do
    it "varBaseMul Circuit is Valid for Type2" $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F Fp)) (F Fp) -> AffinePoint (F Fp)
        f = uncurry \{ x: F x, y: F y } (F t) ->
          let
            base = fromAffine @Fp @Vesta.G { x, y }
            result = scalarMul (fieldShift2 t) base
            { x, y } = unsafePartial $ fromJust $ toAffine @Fp result
          in
            { x: F x, y: F y }
        solver = makeSolver (Proxy @(KimchiConstraint Fp)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM Fp (KimchiConstraint Fp) t Identity
          => AffinePoint (FVar Fp)
          -> FVar Fp
          -> Snarky (KimchiConstraint Fp) t Identity (AffinePoint (FVar Fp))
        circuit p t = do
          g <- scaleFast2 @51 p t
          pure g
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F Fp)) (F Fp)))
            (Proxy @(AffinePoint (F Fp)))
            (Proxy @(KimchiConstraint Fp))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Gen (Tuple (AffinePoint (F Fp)) (F Fp))
        gen = do
          p <- EC.genAffinePoint (Proxy @Vesta.G)
          t <- arbitrary
          pure $ Tuple p t
      in
        do
          circuitSpecPure' s KimchiConstraint.eval solver (satisfied f) gen Kimchi.postCondition

fieldShift1 :: forall f f' n. FieldSizeInBits f n => FieldSizeInBits f' n => PrimeField f' => f -> f'
fieldShift1 t =
  let
    coerceViaBits :: f -> f'
    coerceViaBits = packPure <<< unpackPure
    two = one + one
    twoToThe255 = fromBigInt $ toBigInt (one :: Fp) `shl` fromInt 255
  in
    (two * coerceViaBits t) + one + twoToThe255

fieldShift2 :: forall f f' n. FieldSizeInBits f n => FieldSizeInBits f' n => PrimeField f' => f -> f'
fieldShift2 t =
  let
    coerceViaBits :: f -> f'
    coerceViaBits = packPure <<< unpackPure

    twoToThe255 = fromBigInt $ toBigInt (one :: Fq) `shl` fromInt 255
  in
    coerceViaBits t + twoToThe255
