module Test.Snarky.Circuit.Kimchi.EndoMul (spec) where

import Prelude

import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, SizedF, Snarky)
import Snarky.Circuit.Kimchi.EndoMul (endo, endoInv)
import Snarky.Circuit.Kimchi.EndoScalar (expandToEndoScalar)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class FieldSizeInBits, class FrModule, class HasEndo, class WeierstrassCurve, fromAffine, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
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
  => Proxy f
  -> Proxy g
  -> String
  -> Spec Unit
endoSpec _ curveProxy curveName =
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

        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> SizedF 128 (FVar f)
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit p scalar = do
          result <- endo p scalar
          pure result

        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (SizedF 128 (F f))))
            (Proxy @(AffinePoint (F f)))
            (Proxy @(KimchiConstraint f))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Gen (Tuple (AffinePoint (F f)) (SizedF 128 (F f)))
        gen = do
          p <- EC.genAffinePoint curveProxy
          scalar <- arbitrary
          pure $ Tuple p scalar

      circuitSpecPure' 100
        { builtState: s
        , checker: Kimchi.eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: Kimchi.postCondition
        }
        gen

      liftEffect $ verifyCircuit { s, gen, solver }

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
  => Proxy f
  -> Proxy g
  -> String
  -> Spec Unit
endoInvSpec _ curveProxy curveName =
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

        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> SizedF 128 (FVar f)
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit p scalar = endoInv @f @f' @g p scalar

        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (SizedF 128 (F f))))
            (Proxy @(AffinePoint (F f)))
            (Proxy @(KimchiConstraint f))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Gen (Tuple (AffinePoint (F f)) (SizedF 128 (F f)))
        gen = do
          p <- EC.genAffinePoint curveProxy
          scalar <- arbitrary
          pure $ Tuple p scalar

      circuitSpecPure' 100
        { builtState: s
        , checker: Kimchi.eval
        , solver: solver
        , testFunction: satisfied refFn
        , postCondition: Kimchi.postCondition
        }
        gen

      liftEffect $ verifyCircuit { s, gen, solver }

spec :: Spec Unit
spec = do
  endoSpec (Proxy @Vesta.ScalarField) (Proxy @Pallas.G) "Pallas"
  endoSpec (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) "Vesta"
  endoInvSpec (Proxy @Vesta.ScalarField) (Proxy @Pallas.G) "Pallas"
  endoInvSpec (Proxy @Pallas.ScalarField) (Proxy @Vesta.G) "Vesta"
