module Test.Snarky.Circuit.Kimchi.GenericTest
  ( spec
  ) where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Builder (CircuitBuilderState)
import Snarky.Backend.Compile (Solver, compilePure, makeSolver)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.Curves (add_)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (class KimchiVerify, AuxState, KimchiConstraint, KimchiGate)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class WeierstrassCurve)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, addAffine, genAffinePoint, toAffine)
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
   . KimchiConstraint.KimchiVerify f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => KimchiVerify f f'
  => CircuitGateConstructor f g'
  => String
  -> Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec' testName pg pc =
  describe ("Kimchi Generic (EC Add): " <> testName) do

    it "unsafeAdd Circuit generates valid Generic constraints" $ unsafePartial do
      let
        f :: Tuple (AffinePoint (F f)) (AffinePoint (F f)) -> AffinePoint (F f)
        f (Tuple x y) = unsafePartial $ fromJust $ toAffine $ addAffine x y

        s :: CircuitBuilderState (KimchiGate f) (AuxState f)
        s =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(AffinePoint (F f)))
            pc
            (uncurry add_)
            Kimchi.initialState

        solver :: Solver f (KimchiGate f) (Tuple (AffinePoint (F f)) (AffinePoint (F f))) (AffinePoint (F f))
        solver = makeSolver pc (uncurry add_)

        gen = do
          p1 <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p ->
            let
              { x: x1, y: y1 } = p1
              { x: x2, y: y2 } = p
            in
              x1 /= x2 && y1 /= negate y2
          pure $ Tuple p1 p2

      circuitSpecPure'
        { builtState: s
        , checker: KimchiConstraint.eval
        , solver: solver
        , testFunction: satisfied f
        , postCondition: Kimchi.postCondition
        }
        gen

      liftEffect $ verifyCircuit { s, gen, solver }