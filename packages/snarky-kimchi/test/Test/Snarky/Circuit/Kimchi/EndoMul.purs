module Test.Snarky.Circuit.Kimchi.EndoMul (spec) where

import Prelude

import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Ord (abs)
import Data.Reflectable (class Reflectable)
import Data.Tuple (Tuple(..), uncurry)
import Partial.Unsafe (unsafePartial)
import Prim.Int (class Add)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky)
import Snarky.Circuit.DSL.Bits (packPure, unpackPure)
import Snarky.Circuit.Kimchi.EndoMul (endo)
import Snarky.Circuit.Types (F, FVar)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class PrimeField, class WeierstrassCurve, fromAffine, fromInt, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Snarky.Data.Vector as Vector
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

gen128BitElem :: forall f n _l. FieldSizeInBits f n => Reflectable _l Int => Add 128 _l n => Gen (F f)
gen128BitElem = do
  v <- Vector.generator (Proxy @128) arbitrary
  let v' = v `Vector.append` (Vector.generate $ const false)
  pure $ F $ packPure v'

endoSpec
  :: forall f f' g
   . PrimeField f
  => FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => KimchiVerify f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => FrModule f' g
  => Proxy f
  -> Proxy g
  -> String
  -> Spec Unit
endoSpec _ curveProxy curveName =
  describe ("EndoMul " <> curveName) do
    it ("EndoMul circuit is valid for " <> curveName) $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F f)) (F f) -> AffinePoint (F f)
        f (Tuple { x: F x, y: F y } (F scalar)) =
          let
            coerceViaBits :: f -> f'
            coerceViaBits = packPure <<< unpackPure
            base = fromAffine @f @g { x, y }
            result = scalarMul (coerceViaBits scalar) base
            { x, y } = unsafePartial $ fromJust $ toAffine @f result
          in
            { x: F x, y: F y }

        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> FVar f
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit p scalar = do
          result <- endo p scalar
          pure result

        { constraints } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (F f)))
            (Proxy @(AffinePoint (F f)))
            (Proxy @(KimchiConstraint f))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Gen (Tuple (AffinePoint (F f)) (F f))
        gen = do
          p <- EC.genAffinePoint curveProxy
          scalar <- gen128BitElem
          pure $ Tuple p scalar
      in
        circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen

spec :: Spec Unit
spec = do
  endoSpec (Proxy @Vesta.ScalarField) (Proxy @Pallas.G) "Pallas"
  endoSpec (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) "Vesta"