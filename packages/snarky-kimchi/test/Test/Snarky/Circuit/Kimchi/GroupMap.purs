module Test.Snarky.Circuit.Kimchi.GroupMap
  ( spec
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Effect.Class (liftEffect)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.GroupMap (GroupMapParams, groupMap, groupMapCircuit, groupMapParams)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class HasBW19, class HasSqrt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Pasta (pallasGroupMap, vestaGroupMap)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint)
import Test.QuickCheck (arbitrary, quickCheck')
import Test.Snarky.Circuit.Utils (TestConfig, circuitTest', satisfied)
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

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

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

    it "circuit matches groupMap and satisfies constraints" do
      let
        f :: F f -> AffinePoint (F f)
        f (F t) =
          let
            { x, y } = groupMap params t
          in
            { x: F x, y: F y }

        circuit'
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => FVar f
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit' = groupMapCircuit params

      void $ circuitTest' @f 10
        kimchiTestConfig
        ( NEA.singleton
            { testFunction: satisfied f
            , gen: arbitrary
            }
        )
        circuit'

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
