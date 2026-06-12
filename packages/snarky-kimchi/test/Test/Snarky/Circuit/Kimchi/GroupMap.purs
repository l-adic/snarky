module Test.Snarky.Circuit.Kimchi.GroupMap
  ( spec
  ) where

import Prelude

import Data.Array.NonEmpty as NEA
import Effect.Class (liftEffect)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (F(..), FVar, Snarky)
import Snarky.Circuit.Kimchi.GroupMap (GroupMapParams, groupMap, groupMapCircuit, groupMapParams)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class HasBW19, class HasSqrt, class PrimeField)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Test.QuickCheck (arbitrary, quickCheck')
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
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
    AffinePoint { x, y } = groupMap params t
  in
    y * y == x * x * x + params.b

-- (`testMatchesRustFFI` removed alongside snarky-crypto's BW19 hash-to-curve.
-- That parity test compared PastaCurve's Shallue–vdW `groupMap` against
-- snarky-crypto's Brier–Williams 2019 — two different algorithms; the test
-- never could have passed and was test-only scaffolding.)

spec'
  :: forall f f' g g'
   . HasSqrt f
  => HasBW19 f g
  => CircuitGateConstructor f g'
  => KimchiVerify f f'
  => TestConfig f (KimchiGate f) (AuxState f)
  -> Proxy g
  -> String
  -> Spec Unit
spec' cfg proxyG curveName = do
  let params = groupMapParams proxyG

  describe ("GroupMap: " <> curveName) do
    it "produces valid curve points (y² = x³ + b)"
      $ liftEffect
      $ quickCheck' 100 (testValidCurvePoints params)

    it "circuit matches groupMap and satisfies constraints" do
      let
        f :: F f -> AffinePoint f
        f (F t) =
          let
            AffinePoint { x, y } = groupMap params t
          in
            AffinePoint { x, y }

        circuit'
          :: PrimeField f
          => FVar f
          -> Snarky f (KimchiConstraint f) () (AffinePoint (FVar f))
        circuit' = groupMapCircuit params

      void $ circuitTest' @f
        cfg
        ( NEA.singleton
            { testFunction: satisfied f
            , input: QuickCheck 10 arbitrary
            }
        )
        circuit'

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = describe "GroupMap" do
  spec' cfg (Proxy @Pallas.G) "Pallas"
  spec' cfg (Proxy @Vesta.G) "Vesta"
