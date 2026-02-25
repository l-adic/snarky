module Test.Snarky.Circuit.Curves.Main where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Builder (class CompileCircuit, initialState)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.Curves (add_, assertOnCurve, double)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.DSL (class CircuitM, Basic, BoolVar, F(..), FVar, Snarky, assertEq, if_)
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams, addAffine, genAffinePoint, toAffine)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, frequency)
import Test.Snarky.Circuit.Utils (Expectation, TestConfig, TestInput(..), circuitTest', nullPostCondition, satisfied, satisfied_, unsatisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

basicTestConfig :: forall f. PrimeField f => TestConfig f (Basic f) Unit
basicTestConfig = { checker: Basic.eval, postCondition: nullPostCondition, initState: initialState }

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec (Proxy @Vesta.G) (Proxy @(Basic Vesta.BaseField))

spec
  :: forall g f
   . CompileCircuit f (Basic f) (Basic f) Unit
  => SolveCircuit f (Basic f)
  => Arbitrary g
  => WeierstrassCurve f g
  => Proxy g
  -> Proxy (Basic f)
  -> Spec Unit
spec pg _pc =
  describe "Snarky.Circuit.Curves" do

    it "assertOnCurve Circuit is Valid" do
      let
        { a, b } = curveParams pg

        circuit'
          :: forall t
           . CircuitM f (Basic f) t Identity
          => Tuple (CurveParams (FVar f)) (AffinePoint (FVar f))
          -> Snarky (Basic f) t Identity Unit
        circuit' = uncurry assertOnCurve

        onCurve = do
          p :: AffinePoint (F f) <- genAffinePoint pg
          pure $ Tuple { a: F a, b: F b } p

        offCurve :: Gen (Tuple (CurveParams (F f)) (AffinePoint (F f)))
        offCurve = do
          let { a, b } = curveParams pg
          x <- arbitrary
          y <- arbitrary `suchThat` \_y -> _y * _y /= x * x * x + F a * x + F b
          pure $ Tuple { a: F a, b: F b } { x, y }

      void $ circuitTest' @f
        basicTestConfig
        ( NEA.cons'
            { testFunction: (unsatisfied :: _ -> Expectation Unit)
            , input: QuickCheck 100 offCurve
            }
            [ { testFunction: satisfied_
              , input: QuickCheck 100 onCurve
              }
            ]
        )
        circuit'

    it "assertEqual Circuit is Valid" do
      let
        circuit'
          :: forall t
           . CircuitM f (Basic f) t Identity
          => Tuple (AffinePoint (FVar f)) (AffinePoint (FVar f))
          -> Snarky (Basic f) t Identity Unit
        circuit' = uncurry assertEq

        same = do
          p :: AffinePoint (F f) <- genAffinePoint pg
          pure $ Tuple p p
        distinct = do
          p1 :: AffinePoint (F f) <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p -> p /= p1
          pure $ Tuple p1 p2

      void $ circuitTest' @f
        basicTestConfig
        ( NEA.cons'
            { testFunction: satisfied_
            , input: QuickCheck 100 same
            }
            [ { testFunction: (unsatisfied :: _ -> Expectation Unit)
              , input: QuickCheck 100 distinct
              }
            ]
        )
        circuit'

    it "negate Circuit is Valid" do
      let
        pureNegate :: AffinePoint (F f) -> AffinePoint (F f)
        pureNegate { x, y } = { x, y: negate y }

        circuit'
          :: forall t
           . CircuitM f (Basic f) t Identity
          => AffinePoint (FVar f)
          -> Snarky (Basic f) t Identity (AffinePoint (FVar f))
        circuit' = Curves.negate

        gen = genAffinePoint pg

      void $ circuitTest' @f
        basicTestConfig
        ( NEA.singleton
            { testFunction: satisfied pureNegate
            , input: QuickCheck 100 gen
            }
        )
        circuit'

    it "if_ Circuit is Valid" do
      let
        pureIf :: Tuple3 Boolean (AffinePoint (F f)) (AffinePoint (F f)) -> AffinePoint (F f)
        pureIf = uncurry3 \b then_ else_ -> if b then then_ else else_

        circuit'
          :: forall t
           . CircuitM f (Basic f) t Identity
          => Tuple3 (BoolVar f) (AffinePoint (FVar f)) (AffinePoint (FVar f))
          -> Snarky (Basic f) t Identity (AffinePoint (FVar f))
        circuit' = uncurry3 if_

        gen = do
          b <- arbitrary
          frequency $ NEA.cons'
            ( Tuple 1.0 do
                p <- genAffinePoint pg
                pure $ tuple3 b p p
            )
            [ Tuple 1.0 do
                p1 <- genAffinePoint pg
                p2 <- genAffinePoint pg
                pure $ tuple3 b p1 p2
            ]

      void $ circuitTest' @f
        basicTestConfig
        ( NEA.singleton
            { testFunction: satisfied pureIf
            , input: QuickCheck 100 gen
            }
        )
        circuit'

    it "unsafeAdd Circuit is Valid" $ unsafePartial do
      let
        f (Tuple x y) = unsafePartial $ fromJust $ toAffine $ addAffine x y

        circuit'
          :: forall t
           . CircuitM f (Basic f) t Identity
          => Tuple (AffinePoint (FVar f)) (AffinePoint (FVar f))
          -> Snarky (Basic f) t Identity (AffinePoint (FVar f))
        circuit' = uncurry add_

        -- Generate distinct points to avoid division by zero in slope calculation
        -- Avoid x1 = x2
        gen = do
          p1 <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p ->
            let
              { x: x1, y: y1 } = p1
              { x: x2, y: y2 } = p
            in
              x1 /= x2 && y1 /= negate y2
          pure $ Tuple p1 p2

      void $ circuitTest' @f
        basicTestConfig
        ( NEA.singleton
            { testFunction: satisfied f
            , input: QuickCheck 100 gen
            }
        )
        circuit'

    it "double Circuit is Valid" do
      let
        pureDouble :: AffinePoint (F f) -> AffinePoint (F f)
        pureDouble { x, y } =
          let
            { a } = curveParams pg
            lambda = (three * x * x + F a) / (two * y)
            x' = lambda * lambda - two * x
            y' = lambda * (x - x') - y
            two = F (one + one)
            three = F (one + one + one)
          in
            { x: x', y: y' }

        circuit'
          :: forall t
           . CircuitM f (Basic f) t Identity
          => AffinePoint (FVar f)
          -> Snarky (Basic f) t Identity (AffinePoint (FVar f))
        circuit' = double (curveParams pg)

        -- Generate points where y ≠ 0 to avoid division by zero in doubling
        gen = genAffinePoint pg `suchThat` \{ y } -> y /= zero

      void $ circuitTest' @f
        basicTestConfig
        ( NEA.singleton
            { testFunction: satisfied pureDouble
            , input: QuickCheck 100 gen
            }
        )
        circuit'
