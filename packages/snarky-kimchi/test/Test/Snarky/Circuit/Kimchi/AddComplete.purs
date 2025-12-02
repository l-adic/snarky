module Test.Snarky.Circuit.Kimchi.AddComplete where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Identity (Identity)
import Data.Tuple (Tuple(..), uncurry)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.DSL (class CircuitM, Snarky, const_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Types (F, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class WeierstrassCurve)
import Snarky.Data.EllipticCurve (Point(..), AffinePoint)
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall g f
   . Arbitrary f
  => Arbitrary g
  => Eq f
  => WeierstrassCurve f g
  => Proxy g
  -> Spec Unit
spec pg =
  describe "Kimchi AddComplete" do

    it "addComplete Circuit is Valid" $
      let
        f = uncurry EC.addAffine
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

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
          pure $ Point { x, y, z }
        { constraints } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(Point (F f)))
            (uncurry circuit)

        -- Generate distinct points to avoid division by zero in slope calculation
        -- Avoid x1 = x2
        gen = do
          p1 <- EC.genAffinePoint pg
          p2 <- EC.genAffinePoint pg `suchThat` \p ->
            let
              { x: x1, y: y1 } = p1
              { x: x2, y: y2 } = p
            in
              x1 /= x2 || y1 /= negate y2
          pure $ Tuple p1 p2
        genInverse = do
          p1 <- EC.genAffinePoint pg
          let p2 = p1 { y = -p1.y }
          pure $ Tuple p1 p2

      in
        do
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) genInverse