module Test.Snarky.Circuit.Curves.Main where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Array.NonEmpty as NEA
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Builder (class CompileCircuit, initialState)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Prover (class SolveCircuit)
import Snarky.Circuit.Curves (add_, assertEqual, assertOnCurve, double, if_)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.Types (F(..))
import Snarky.Constraint.Basic (Basic)
import Snarky.Constraint.Basic as Basic
import Snarky.Curves.Class (class WeierstrassCurve, curveParams)
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, CurveParams, addAffine, genAffinePoint, toAffine)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, frequency)
import Test.Snarky.Circuit.Utils (circuitSpecPure', nullPostCondition, satisfied, satisfied_, unsatisfied)
import Test.Spec (Spec, describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

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
spec pg pc =
  describe "Snarky.Circuit.Curves" do

    it "assertOnCurve Circuit is Valid" $
      let
        { a, b } = curveParams pg
        solver = makeSolver pc (uncurry assertOnCurve)
        s =
          compilePure
            ( Proxy
                @( Tuple
                    (CurveParams (F f))
                    (AffinePoint (F f))
                )
            )
            (Proxy @Unit)
            pc
            (uncurry assertOnCurve)
            initialState

        onCurve = do
          p :: AffinePoint (F f) <- genAffinePoint pg
          pure $ Tuple { a: F a, b: F b } p

        offCurve :: Gen (Tuple (CurveParams (F f)) (AffinePoint (F f)))
        offCurve = do
          let { a, b } = curveParams pg
          x <- arbitrary
          y <- arbitrary `suchThat` \_y -> _y * _y /= x * x * x + F a * x + F b
          pure $ Tuple { a: F a, b: F b } { x, y }
      in
        do
          circuitSpecPure'
            { builtState: s
            , checker: Basic.eval
            , solver: solver
            , testFunction: unsatisfied
            , postCondition: nullPostCondition
            }
            offCurve
          circuitSpecPure'
            { builtState: s
            , checker: Basic.eval
            , solver: solver
            , testFunction: satisfied_
            , postCondition: nullPostCondition
            }
            onCurve

    it "assertEqual Circuit is Valid" $
      let
        solver = makeSolver (Proxy @(Basic f)) (uncurry assertEqual)
        s =
          compilePure
            ( Proxy
                @( Tuple
                    (AffinePoint (F f))
                    (AffinePoint (F f))
                )
            )
            (Proxy @Unit)
            pc
            (uncurry assertEqual)
            initialState

        same = do
          p :: AffinePoint (F f) <- genAffinePoint pg
          pure $ Tuple p p
        distinct = do
          p1 :: AffinePoint (F f) <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p -> p /= p1
          pure $ Tuple p1 p2
      in
        do
          circuitSpecPure'
            { builtState: s
            , checker: Basic.eval
            , solver: solver
            , testFunction: satisfied_
            , postCondition: nullPostCondition
            }
            same
          circuitSpecPure'
            { builtState: s
            , checker: Basic.eval
            , solver: solver
            , testFunction: unsatisfied
            , postCondition: nullPostCondition
            }
            distinct

    it "negate Circuit is Valid" $
      let
        pureNegate :: AffinePoint (F f) -> AffinePoint (F f)
        pureNegate { x, y } = { x, y: negate y }
        solver = makeSolver (Proxy @(Basic f)) Curves.negate
        s =
          compilePure
            (Proxy @(AffinePoint (F f)))
            (Proxy @(AffinePoint (F f)))
            pc
            Curves.negate
            initialState
        gen = genAffinePoint pg
      in
        circuitSpecPure'
          { builtState: s
          , checker: Basic.eval
          , solver: solver
          , testFunction: (satisfied pureNegate)
          , postCondition: nullPostCondition
          }
          gen

    it "if_ Circuit is Valid" $
      let
        pureIf :: Tuple3 Boolean (AffinePoint (F f)) (AffinePoint (F f)) -> AffinePoint (F f)
        pureIf = uncurry3 \b then_ else_ -> if b then then_ else else_
        solver = makeSolver (Proxy @(Basic f)) (uncurry3 if_)
        s =
          compilePure
            (Proxy @(Tuple3 Boolean (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(AffinePoint (F f)))
            pc
            (uncurry3 if_)
            initialState
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
      in
        circuitSpecPure'
          { builtState: s
          , checker: Basic.eval
          , solver: solver
          , testFunction: (satisfied pureIf)
          , postCondition: nullPostCondition
          }
          gen

    it "unsafeAdd Circuit is Valid" $ unsafePartial $
      let
        f (Tuple x y) = unsafePartial $ fromJust $ toAffine $ addAffine x y
        solver = makeSolver (Proxy @(Basic f)) (uncurry add_)
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(AffinePoint (F f)))
            pc
            (uncurry add_)
            initialState

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
      in
        circuitSpecPure'
          { builtState: s
          , checker: Basic.eval
          , solver: solver
          , testFunction: (satisfied f)
          , postCondition: nullPostCondition
          }
          gen

    it "double Circuit is Valid" $
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

        solver = makeSolver (Proxy @(Basic f)) (double $ curveParams pg)
        s =
          compilePure
            (Proxy @(AffinePoint (F f)))
            (Proxy @(AffinePoint (F f)))
            pc
            (double $ curveParams pg)
            initialState

        -- Generate points where y ≠ 0 to avoid division by zero in doubling
        gen = genAffinePoint pg `suchThat` \{ y } -> y /= zero
      in
        circuitSpecPure'
          { builtState: s
          , checker: Basic.eval
          , solver: solver
          , testFunction: (satisfied pureDouble)
          , postCondition: nullPostCondition
          }
          gen