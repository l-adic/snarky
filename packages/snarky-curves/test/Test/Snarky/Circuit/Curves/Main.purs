module Test.Snarky.Circuit.Curves.Main where

import Prelude

import Data.Identity (Identity(..))
import Data.Newtype (un)
import Data.Tuple (Tuple(..), uncurry)
import Effect (Effect)
import Snarky.Circuit.Compile (compile, makeSolver)
import Snarky.Circuit.Curves (assertOnCurve)
import Snarky.Circuit.Curves.Types (AffinePoint(..), CurveParams(..), genAffinePoint)
import Snarky.Circuit.TestUtils (ConstraintSystem, assertionSpec')
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