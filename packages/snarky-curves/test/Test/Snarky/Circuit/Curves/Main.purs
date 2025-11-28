module Test.Snarky.Circuit.Curves.Main where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Tuple (Tuple(..), uncurry)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Effect (Effect)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.Backend.Compile (compilePure, makeSolver)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied, satisfied_, unsatisfied)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Circuit.Curves (addComplete, add_, assertEqual, assertOnCurve, double, if_)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.Curves.Types (AffinePoint, CurveParams, Point, genAffinePoint)
import Snarky.Circuit.DSL (class CircuitM, Snarky, const_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Circuit.Types (F(..), FVar)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve, curveParams)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, frequency)
import Test.Spec (Spec, describe, it)
import Test.Spec.Reporter.Console (consoleReporter)
import Test.Spec.Runner.Node (runSpecAndExitProcess)
import Type.Proxy (Proxy(..))

main :: Effect Unit
main =
  runSpecAndExitProcess [ consoleReporter ] do
    spec (Proxy @Vesta.G)

spec
  :: forall g f
   . Arbitrary f
  => Arbitrary g
  => Eq f
  => WeierstrassCurve f g
  => Proxy g
  -> Spec Unit
spec pg =
  describe "Snarky.Circuit.Curves" do

    it "assertOnCurve Circuit is Valid" $
      let
        { a, b } = curveParams pg
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry assertOnCurve)
        { constraints } =
          compilePure
            ( Proxy
                @( Tuple
                    (CurveParams (F f))
                    (AffinePoint (F f))
                )
            )
            (Proxy @Unit)
            (uncurry assertOnCurve)

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
          circuitSpecPure' constraints KimchiConstraint.eval solver unsatisfied offCurve
          circuitSpecPure' constraints KimchiConstraint.eval solver satisfied_ onCurve

    it "assertEqual Circuit is Valid" $
      let
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry assertEqual)
        { constraints } =
          compilePure
            ( Proxy
                @( Tuple
                    (AffinePoint (F f))
                    (AffinePoint (F f))
                )
            )
            (Proxy @Unit)
            (uncurry assertEqual)

        same = do
          p :: AffinePoint (F f) <- genAffinePoint pg
          pure $ Tuple p p
        distinct = do
          p1 :: AffinePoint (F f) <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p -> p /= p1
          pure $ Tuple p1 p2
      in
        do
          circuitSpecPure' constraints KimchiConstraint.eval solver satisfied_ same
          circuitSpecPure' constraints KimchiConstraint.eval solver unsatisfied distinct

    it "negate Circuit is Valid" $
      let
        pureNegate :: AffinePoint (F f) -> AffinePoint (F f)
        pureNegate { x, y } = { x, y: negate y }
        solver = makeSolver (Proxy @(KimchiConstraint f)) Curves.negate
        { constraints } =
          compilePure
            (Proxy @(AffinePoint (F f)))
            (Proxy @(AffinePoint (F f)))
            Curves.negate
        gen = genAffinePoint pg
      in
        circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied pureNegate) gen

    it "if_ Circuit is Valid" $
      let
        pureIf :: Tuple3 Boolean (AffinePoint (F f)) (AffinePoint (F f)) -> AffinePoint (F f)
        pureIf = uncurry3 \b then_ else_ -> if b then then_ else else_
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry3 if_)
        { constraints } =
          compilePure
            (Proxy @(Tuple3 Boolean (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(AffinePoint (F f)))
            (uncurry3 if_)
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
        circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied pureIf) gen

    it "unsafeAdd Circuit is Valid" $ unsafePartial $
      let
        f = uncurry ecAdd
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry add_)
        { constraints } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(AffinePoint (F f)))
            (uncurry add_)

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
        circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen

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

        solver = makeSolver (Proxy @(KimchiConstraint f)) (double pg)
        { constraints } =
          compilePure
            (Proxy @(AffinePoint (F f)))
            (Proxy @(AffinePoint (F f)))
            (double pg)

        -- Generate points where y ≠ 0 to avoid division by zero in doubling
        gen = genAffinePoint pg `suchThat` \{ y } -> y /= zero
      in
        circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied pureDouble) gen

    it "addComplete Circuit is Valid" $
      let
        f = uncurry (ecAddComplete pg)
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

        -- if the result is at infinity, ecAddComplete actually produces garbage 
        -- for the x and y values, they should be 0, 1 respectively
        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> AffinePoint (FVar f)
          -> Snarky t Identity (Point (FVar f))
        circuit p1 p2 = do
          { isInfinity, p } <- addComplete p1 p2
          x <- Snarky.if_ isInfinity (const_ zero) p.x
          y <- Snarky.if_ isInfinity (const_ one) p.y
          z <- Snarky.if_ isInfinity (const_ zero) (const_ one)
          pure { x, y, z }
        { constraints } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(Point (F f)))
            (uncurry circuit)

        -- Generate distinct points to avoid division by zero in slope calculation
        -- Avoid x1 = x2
        gen = do
          p1 <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p ->
            let
              { x: x1, y: y1 } = p1
              { x: x2, y: y2 } = p
            in
              x1 /= x2 || y1 /= negate y2
          pure $ Tuple p1 p2
        genInverse = do
          p1 <- genAffinePoint pg
          let p2 = p1 { y = -p1.y }
          pure $ Tuple p1 p2

      in
        do
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) genInverse

ecAdd
  :: forall f
   . PrimeField f
  => Partial
  => AffinePoint (F f)
  -> AffinePoint (F f)
  -> AffinePoint (F f)
ecAdd { x: x1, y: y1 } { x: x2, y: y2 } =
  let
    lambda = (y2 - y1) / (x2 - x1) -- Assumes x1 ≠ x2
    x3 = (lambda * lambda) - x1 - x2
    y3 = lambda * (x1 - x3) - y1
  in
    { x: x3, y: y3 }

ecAddComplete
  :: forall f g
   . WeierstrassCurve f g
  => Proxy g
  -> AffinePoint (F f)
  -> AffinePoint (F f)
  -> Point (F f)
ecAddComplete _ p1 p2 =
  if p1.x == p2.x && p1.y == negate p2.y then { x: zero, y: one, z: zero }
  else
    let
      { x, y } = unsafePartial $ ecAdd p1 p2
    in
      { x, y, z: one }
