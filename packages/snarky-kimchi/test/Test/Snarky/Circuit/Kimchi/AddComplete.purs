module Test.Snarky.Circuit.Kimchi.AddComplete (spec) where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Identity (Identity)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (class CircuitM, Snarky, const_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Circuit.Kimchi.AddComplete (addComplete)
import Snarky.Circuit.Types (F, FVar)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Curves.Class (class WeierstrassCurve)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, Point(..))
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary)
import Test.Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = do
  spec' "Vesta" (Proxy @Vesta.G) (Proxy @(KimchiConstraint Vesta.BaseField))
  spec' "Pallas" (Proxy @Pallas.G) (Proxy @(KimchiConstraint Pallas.BaseField))

spec'
  :: forall g g' f f'
   . Kimchi.KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Arbitrary g
  => WeierstrassCurve f g
  => String
  -> Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec' testName pg pc =
  describe ("Kimchi AddComplete: " <> testName) do

    it "addComplete Circuit is Valid" $ unsafePartial $
      let
        f = uncurry EC.addAffine
        solver = makeSolver (Proxy @(KimchiConstraint f)) (uncurry circuit)

        circuit
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => AffinePoint (FVar f)
          -> AffinePoint (FVar f)
          -> Snarky (KimchiConstraint f) t Identity (Point (FVar f))
        circuit p1 p2 = do
          { isInfinity, p } <- addComplete p1 p2
          x <- Snarky.if_ isInfinity (const_ zero) p.x
          y <- Snarky.if_ isInfinity (const_ one) p.y
          z <- Snarky.if_ isInfinity (const_ zero) (const_ one)
          pure $ Point { x, y, z }
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(Point (F f)))
            pc
            (uncurry circuit)
            Kimchi.initialState

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
          circuitSpecPure'
            { builtState: s
            , checker: Kimchi.eval
            , solver: solver
            , testFunction: satisfied f
            , postCondition: Kimchi.postCondition
            }
            gen
          liftEffect $ verifyCircuit { s, gen, solver }

          circuitSpecPure'
            { builtState: s
            , checker: Kimchi.eval
            , solver: solver
            , testFunction: satisfied f
            , postCondition: Kimchi.postCondition
            }
            genInverse
          liftEffect $ verifyCircuit { s, gen: genInverse, solver }