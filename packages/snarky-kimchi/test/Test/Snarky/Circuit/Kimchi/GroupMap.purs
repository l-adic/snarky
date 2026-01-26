module Test.Snarky.Circuit.Kimchi.GroupMap
  ( spec
  ) where

import Prelude

import Effect.Class (liftEffect)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.GroupMap (GroupMapParams, groupMap, groupMapCircuit, groupMapParams)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class HasBW19, class HasSqrt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (pallasGroupMap, vestaGroupMap)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.QuickCheck (arbitrary, quickCheck')
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

-- | Test that groupMap produces valid curve points (y² = x³ + b)
testValidCurvePoints
  :: forall f
   . HasSqrt f
  => GroupMapParams f
  -> F f
  -> Boolean
testValidCurvePoints params (F t) =
  let
    { x, y } = groupMap params t
  in
    y * y == x * x * x + params.b

-- | Test that groupMap matches the Rust FFI implementation
testMatchesRustFFI
  :: forall f
   . HasSqrt f
  => Eq f
  => GroupMapParams f
  -> (f -> { x :: f, y :: f })
  -> F f
  -> Boolean
testMatchesRustFFI params rustGroupMap (F t) =
  let
    psResult = groupMap params t
    rustResult = rustGroupMap t
  in
    psResult.x == rustResult.x && psResult.y == rustResult.y

spec'
  :: forall f f' g g'
   . HasSqrt f
  => HasBW19 f g
  => CircuitGateConstructor f g'
  => KimchiVerify f f'
  => Proxy g
  -> String
  -> Spec Unit
spec' proxyG curveName = do
  let params = groupMapParams proxyG

  describe ("GroupMap: " <> curveName) do
    it "produces valid curve points (y² = x³ + b)"
      $ liftEffect
      $ quickCheck' 100 (testValidCurvePoints params)

    it "circuit matches groupMap and satisfies constraints" $
      let
        f :: F f -> AffinePoint (F f)
        f (F t) =
          let
            { x, y } = groupMap params t
          in
            { x: F x, y: F y }

        circuit
          :: forall t m
           . CircuitM f (KimchiConstraint f) t m
          => FVar f
          -> Snarky (KimchiConstraint f) t m (AffinePoint (FVar f))
        circuit = groupMapCircuit params

        solver = makeSolver (Proxy @(KimchiConstraint f)) circuit

        s = compilePure
          (Proxy @(F f))
          (Proxy @(AffinePoint (F f)))
          (Proxy @(KimchiConstraint f))
          circuit
          Kimchi.initialState

      in
        circuitSpecPure' 10
          { builtState: s
          , checker: Kimchi.eval
          , solver: solver
          , testFunction: satisfied f
          , postCondition: Kimchi.postCondition
          }
          arbitrary

spec :: Spec Unit
spec = do
  describe "GroupMap" do
    spec' (Proxy @Pallas.G) "Pallas"
    spec' (Proxy @Vesta.G) "Vesta"

    it "Pallas groupMap matches Rust FFI"
      $ liftEffect
      $ quickCheck' 100
      $
        testMatchesRustFFI (groupMapParams (Proxy @Pallas.G)) pallasGroupMap

    it "Vesta groupMap matches Rust FFI"
      $ liftEffect
      $ quickCheck' 100
      $
        testMatchesRustFFI (groupMapParams (Proxy @Vesta.G)) vestaGroupMap
