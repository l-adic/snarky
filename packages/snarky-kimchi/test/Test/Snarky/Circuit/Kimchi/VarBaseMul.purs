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
import Snarky.Circuit.Kimchi.VarBaseMul (varBaseMul)
import Snarky.Circuit.Types (F, FVar)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class WeierstrassCurve, fromAffine, fromBigInt, scalarMul, toAffine, toBigInt)
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Snarky.Types.Shifted (class Shifted, Type1(..))
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall g f f'
   . KimchiVerify f
  => Arbitrary g
  => WeierstrassCurve f g -- g is defined over f
  => FrModule f' g
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => Shifted Type1 f
  => Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec pg pc =
  describe "VarBaseMul" do
    it "varBaseMul Circuit is Valid" $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F f)) (Type1 (F f)) -> AffinePoint (F f)
        f (Tuple { x: F x, y: F y } (Type1 (F t))) =
          let
            coerceViaBits :: f -> f'
            coerceViaBits = packPure <<< unpackPure

            unshiftedScalar :: f'
            unshiftedScalar =
              let
                two = one + one
                twoToThe255 = fromBigInt $ toBigInt (one :: f') `shl` fromInt 255
              in
                (two * coerceViaBits t) + one + twoToThe255

            { x, y } = unsafePartial $ fromJust $ toAffine @f @g $ scalarMul unshiftedScalar (fromAffine { x, y })
          in
            { x: F x, y: F y }
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> Type1 (FVar f)
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit p t = do
          { g, k: (Proxy :: Proxy 51) } <- varBaseMul p t
          pure g
        { constraints } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (Type1 (F f))))
            (Proxy @(AffinePoint (F f)))
            pc
            (uncurry circuit)
            Kimchi.initialState

        gen :: Shifted Type1 f => Gen (Tuple (AffinePoint (F f)) (Type1 (F f)))
        gen = do
          p <- EC.genAffinePoint pg
          t <- arbitrary
          pure $ Tuple p (Type1 t)
      in
        do
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen