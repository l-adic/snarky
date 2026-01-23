module Test.Snarky.Circuit.Kimchi.VarBaseMul where

import Prelude

import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, F(..), Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Circuit.Kimchi.VarBaseMul (scaleFast1, scaleFast2)
import Snarky.Circuit.Types (BoolVar, F, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (fromAffine, scalarMul, toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Snarky.Types.Shifted (Type1, Type2, fromShifted, toShifted)
import Test.QuickCheck (arbitrary)
import Test.QuickCheck.Gen (Gen)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  -- Type1: Vesta circuit (field = Vesta.BaseField)
  -- Uses Vesta.G curve (coordinates in Vesta.BaseField = circuit field)
  -- Scalars are in Vesta.ScalarField (smaller than circuit field)
  describe "VarBaseMul Type1 (Vesta circuit)" do
    it "varBaseMul Circuit is Valid for Type1" $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F Vesta.BaseField)) (Type1 (F Vesta.BaseField)) -> AffinePoint (F Vesta.BaseField)
        f (Tuple { x: F x, y: F y } scalar_) =
          let
            base = fromAffine @Vesta.BaseField @Vesta.G { x, y }
            scalar = case fromShifted scalar_ of F a -> a
            result = scalarMul scalar base
            { x: x', y: y' } = unsafePartial $ fromJust $ toAffine @Vesta.BaseField result
          in
            { x: F x', y: F y' }
        solver = makeSolver (Proxy @(KimchiConstraint Vesta.BaseField)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM Vesta.BaseField (KimchiConstraint Vesta.BaseField) t Identity
          => AffinePoint (FVar Vesta.BaseField)
          -> Type1 (FVar Vesta.BaseField)
          -> Snarky (KimchiConstraint Vesta.BaseField) t Identity (AffinePoint (FVar Vesta.BaseField))
        circuit p t = do
          g <- scaleFast1 @51 p t
          pure g
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F Vesta.BaseField)) (Type1 (F Vesta.BaseField))))
            (Proxy @(AffinePoint (F Vesta.BaseField)))
            (Proxy @(KimchiConstraint Vesta.BaseField))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Gen (Tuple (AffinePoint (F Vesta.BaseField)) (Type1 (F Vesta.BaseField)))
        gen = do
          p <- EC.genAffinePoint (Proxy @Vesta.G)
          -- Generate the shifted value directly in the circuit field
          -- (don't go through toShifted which crosses fields)
          t <- arbitrary @(F Vesta.ScalarField)
          pure $ Tuple p (toShifted t)
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

  -- Type2: Pallas circuit, scalar field (Pallas.ScalarField) is LARGER than circuit field (Pallas.BaseField)
  describe "VarBaseMul Type2 (Pallas circuit)" do
    it "varBaseMul Circuit is Valid for Type2" $ unsafePartial $
      let
        f :: Tuple (AffinePoint (F Pallas.BaseField)) (Type2 (F Pallas.BaseField) Boolean) -> AffinePoint (F Pallas.BaseField)
        f (Tuple { x: F x, y: F y } scalar_) =
          let
            base = fromAffine @Pallas.BaseField @Pallas.G { x, y }

            scalar :: Pallas.ScalarField
            scalar = case fromShifted scalar_ of F a -> a
            result = scalarMul scalar base
            { x: x', y: y' } = unsafePartial $ fromJust $ toAffine @Pallas.BaseField result
          in
            { x: F x', y: F y' }
        solver = makeSolver (Proxy @(KimchiConstraint Pallas.BaseField)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM Pallas.BaseField (KimchiConstraint Pallas.BaseField) t Identity
          => AffinePoint (FVar Pallas.BaseField)
          -> Type2 (FVar Pallas.BaseField) (BoolVar Pallas.BaseField)
          -> Snarky (KimchiConstraint Pallas.BaseField) t Identity (AffinePoint (FVar Pallas.BaseField))
        circuit p t = scaleFast2 @51 p t
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F Pallas.BaseField)) (Type2 (F Pallas.BaseField) Boolean)))
            (Proxy @(AffinePoint (F Pallas.BaseField)))
            (Proxy @(KimchiConstraint Pallas.BaseField))
            (uncurry circuit)
            Kimchi.initialState

        gen :: Gen (Tuple (AffinePoint (F Pallas.BaseField)) (Type2 (F Pallas.BaseField) Boolean))
        gen = do
          p <- EC.genAffinePoint (Proxy @Pallas.G)
          circuitVal <- arbitrary @(F Pallas.ScalarField)
          pure $ Tuple p (toShifted circuitVal)
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
