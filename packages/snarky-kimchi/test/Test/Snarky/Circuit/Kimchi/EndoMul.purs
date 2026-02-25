module Test.Snarky.Circuit.Kimchi.EndoMul (spec) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi.EndoMul (endo, endoInv)
import Snarky.Circuit.Kimchi.EndoScalar (expandToEndoScalar)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class WeierstrassCurve, fromAffine, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

endoSpec
  :: forall f f' g g'
   . FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => CircuitGateConstructor f g'
  => KimchiVerify f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => FrModule f' g
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy g
  -> String
  -> Spec Unit
endoSpec cfg _ curveProxy curveName =
  describe ("EndoMul " <> curveName) do
    it ("EndoMul circuit is valid for " <> curveName) $ unsafePartial $ do
      let
        f :: Tuple (AffinePoint (F f)) (SizedF 128 (F f)) -> AffinePoint (F f)
        f (Tuple { x: F x, y: F y } scalar) =
          let
            base = fromAffine @f @g { x, y }
            effectiveScalar = expandToEndoScalar scalar :: F f'
            result = scalarMul (unwrap effectiveScalar) base
            { x, y } = unsafePartial $ fromJust $ toAffine @f result
          in
            { x: F x, y: F y }

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> SizedF 128 (FVar f)
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit p scalar = do
          result <- endo p scalar
          pure result

        gen :: Gen (Tuple (AffinePoint (F f)) (SizedF 128 (F f)))
        gen = do
          p <- EC.genAffinePoint curveProxy
          scalar <- arbitrary
          pure $ Tuple p scalar

      { builtState, solver } <- circuitTest' @f
        cfg
        ( NEA.singleton
            { testFunction: satisfied f
            , input: QuickCheck 100 gen
            }
        )
        (uncurry circuit)

      liftEffect $ verifyCircuit { s: builtState, gen, solver }

endoInvSpec
  :: forall f f' g g'
   . FieldSizeInBits f 255
  => FieldSizeInBits f' 255
  => CircuitGateConstructor f g'
  => KimchiVerify f f'
  => HasEndo f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => FrModule f' g
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy f
  -> Proxy g
  -> String
  -> Spec Unit
endoInvSpec cfg _ curveProxy curveName =
  describe ("EndoInv " <> curveName) do
    it ("EndoInv circuit is valid for " <> curveName) $ unsafePartial $ do
      let
        -- Reference: compute g / scalar using constant operations
        refFn :: Tuple (AffinePoint (F f)) (SizedF 128 (F f)) -> AffinePoint (F f)
        refFn (Tuple { x: F x, y: F y } scalar) =
          let
            -- Convert scalar to effective scalar in f'
            effectiveScalar = expandToEndoScalar scalar :: F f'
            -- Compute inverse
            invScalar = recip effectiveScalar
            -- Scale the point
            base = fromAffine { x, y } :: g
            result = scalarMul (unwrap invScalar) base
            { x, y } = unsafePartial $ fromJust $ toAffine result
          in
            { x: F x, y: F y }

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> SizedF 128 (FVar f)
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit p scalar = endoInv @f @f' @g p scalar

        gen :: Gen (Tuple (AffinePoint (F f)) (SizedF 128 (F f)))
        gen = do
          p <- EC.genAffinePoint curveProxy
          scalar <- arbitrary
          pure $ Tuple p scalar

      { builtState, solver } <- circuitTest' @f
        cfg
        ( NEA.singleton
            { testFunction: satisfied refFn
            , input: QuickCheck 100 gen
            }
        )
        (uncurry circuit)

      liftEffect $ verifyCircuit { s: builtState, gen, solver }

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = do
  endoSpec cfg (Proxy @Vesta.ScalarField) (Proxy @Pallas.G) "Pallas"
  endoSpec cfg (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) "Vesta"
  endoInvSpec cfg (Proxy @Vesta.ScalarField) (Proxy @Pallas.G) "Pallas"
  endoInvSpec cfg (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) "Vesta"
