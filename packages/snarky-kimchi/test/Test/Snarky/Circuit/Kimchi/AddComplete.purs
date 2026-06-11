module Test.Snarky.Circuit.Kimchi.AddComplete (spec) where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Array.NonEmpty as NEA
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Run (EFFECT)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.DSL (FVar, Snarky, const_)
import Snarky.Circuit.DSL as Snarky
import Snarky.Circuit.Kimchi.AddComplete (Finiteness(..), addFast)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class PrimeField, class WeierstrassCurve)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..), Point(..))
import Snarky.Data.EllipticCurve as EC
import Test.QuickCheck (class Arbitrary)
import Test.Snarky.Circuit.Utils (TestConfig, TestInput(..), circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))
import Type.Row (type (+))

spec :: (forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)) -> Spec Unit
spec cfg = do
  spec' cfg "Vesta" (Proxy @Vesta.G) (Proxy @(KimchiConstraint Vesta.BaseField))
  spec' cfg "Pallas" (Proxy @Pallas.G) (Proxy @(KimchiConstraint Pallas.BaseField))

spec'
  :: forall g g' f f'
   . KimchiVerify f f'
  => CircuitGateConstructor f g'
  => Arbitrary g
  => WeierstrassCurve f g
  => TestConfig f (KimchiGate f) (AuxState f)
  -> String
  -> Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec' cfg testName pg _ =
  describe ("Kimchi AddComplete: " <> testName) do

    it "addComplete Circuit is Valid" $ unsafePartial do
      let
        -- `AffinePoint` is a record (stays `F f`-leaved at the circuit
        -- boundary); coerce its inputs to raw `f` so `addAffine` yields the
        -- raw `Point f` the circuit's value side now expects.
        f (Tuple a b) = EC.addAffine a b

        circuit
          :: PrimeField f
          => AffinePoint (FVar f)
          -> AffinePoint (FVar f)
          -> Snarky f (KimchiConstraint f) (EFFECT + ()) (Point (FVar f))
        circuit p1 p2 = do
          { isInfinity, p: AffinePoint p } <- addFast DontCheckFinite p1 p2
          x <- Snarky.if_ isInfinity (const_ zero) p.x
          y <- Snarky.if_ isInfinity (const_ one) p.y
          z <- Snarky.if_ isInfinity (const_ zero) (const_ one)
          pure $ Point { x, y, z }

        -- Generate distinct points to avoid division by zero in slope calculation
        -- Avoid x1 = x2
        gen = do
          p1 <- EC.genAffinePoint pg
          p2 <- EC.genAffinePoint pg `suchThat` \p ->
            let
              AffinePoint { x: x1, y: y1 } = p1
              AffinePoint { x: x2, y: y2 } = p
            in
              x1 /= x2 || y1 /= negate y2
          pure $ Tuple p1 p2
        genInverse = do
          p1 <- EC.genAffinePoint pg
          let p2 = (\(AffinePoint r) -> AffinePoint (r { y = -r.y })) p1
          pure $ Tuple p1 p2

      { builtState, solver } <- circuitTest' @f
        cfg
        ( NEA.cons'
            { testFunction: satisfied f
            , input: QuickCheck 100 gen
            }
            [ { testFunction: satisfied f
              , input: QuickCheck 100 genInverse
              }
            ]
        )
        (uncurry circuit)

      liftEffect $ verifyCircuit { s: builtState, gen, solver }
      liftEffect $ verifyCircuit { s: builtState, gen: genInverse, solver }
