module Test.Snarky.Circuit.Curves.Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Effect (Effect)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.Curves (assertOnCurve, assertEqual)
import Snarky.Circuit.Curves as Curves
import Snarky.Circuit.Curves.Types (AffinePoint(..), CurveParams(..), genAffinePoint)
import Snarky.Circuit.TestUtils (ConstraintSystem, assertionSpec', circuitSpec')
import Snarky.Curves.Class (class WeierstrassCurve, curveParams)
import Snarky.Curves.Vesta as Vesta
import Test.QuickCheck (class Arbitrary)
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
        isValid :: Tuple (CurveParams f) (AffinePoint f) -> Boolean
        isValid (Tuple (CurveParams { a, b }) (AffinePoint { x, y })) =
          let
            y_sq = y * y
            x_sq = x * x
            x_cb = x_sq * x
            rhs = x_cb + a * x + b
          in
            y_sq == rhs
        solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertOnCurve)
        { constraints } = un Identity $
          compile
            ( Proxy
                @( Tuple
                    (CurveParams f)
                    (AffinePoint f)
                )
            )
            (Proxy @Unit)
            (uncurry assertOnCurve)

        gen = do
          p :: AffinePoint f <- genAffinePoint pg
          pure $ Tuple (CurveParams $ curveParams pg) p

      in
        assertionSpec' constraints solver isValid gen

    it "assertEqual Circuit is Valid" $
      let
        isValid :: Tuple (AffinePoint f) (AffinePoint f) -> Boolean
        isValid (Tuple p1 p2) = p1 == p2
        solver = makeSolver (Proxy @(ConstraintSystem f)) (uncurry assertEqual)
        { constraints } = un Identity $
          compile
            ( Proxy
                @( Tuple
                    (AffinePoint f)
                    (AffinePoint f)
                )
            )
            (Proxy @Unit)
            (uncurry assertEqual)

        gen = do
          p :: AffinePoint f <- genAffinePoint pg
          pure $ Tuple p p

      in
        assertionSpec' constraints solver isValid gen

    it "negate Circuit is Valid" $
      let
        pureNegate :: AffinePoint f -> AffinePoint f
        pureNegate (AffinePoint { x, y }) = AffinePoint { x, y: negate y }
        solver = makeSolver (Proxy @(ConstraintSystem f)) Curves.negate
        { constraints } = un Identity $
          compile
            (Proxy @(AffinePoint f))
            (Proxy @(AffinePoint f))
            Curves.negate
        gen = genAffinePoint pg
      in
        circuitSpec' constraints solver pureNegate gen