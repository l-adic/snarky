module Test.Snarky.Circuit.Kimchi.GenericTest
  ( spec
  ) where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Array.NonEmpty as NEA
import Data.Identity (Identity)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Kimchi.Class (class CircuitGateConstructor)
import Snarky.Circuit.Curves (add_)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky)
import Snarky.Circuit.Kimchi.Utils (verifyCircuit)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint, KimchiGate, eval)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi.Types (AuxState)
import Snarky.Curves.Class (class WeierstrassCurve)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint, addAffine, genAffinePoint, toAffine)
import Test.QuickCheck (class Arbitrary)
import Test.Snarky.Circuit.Utils (TestConfig, circuitTest', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

kimchiTestConfig :: forall f f'. KimchiVerify f f' => TestConfig f (KimchiGate f) (AuxState f)
kimchiTestConfig = { checker: eval, postCondition: Kimchi.postCondition, initState: Kimchi.initialState }

spec :: Spec Unit
spec = do
  spec' "Vesta" (Proxy @Vesta.G) (Proxy @(KimchiConstraint Vesta.BaseField))
  spec' "Pallas" (Proxy @Pallas.G) (Proxy @(KimchiConstraint Pallas.BaseField))

spec'
  :: forall g g' f f'
   . KimchiVerify f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => CircuitGateConstructor f g'
  => String
  -> Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec' testName pg _ =
  describe ("Kimchi Generic (EC Add): " <> testName) do

    it "unsafeAdd Circuit generates valid Generic constraints" $ unsafePartial do
      let
        f :: Tuple (AffinePoint (F f)) (AffinePoint (F f)) -> AffinePoint (F f)
        f (Tuple x y) = unsafePartial $ fromJust $ toAffine $ addAffine x y

        circuit'
          :: forall t
           . CircuitM f (KimchiConstraint f) t Identity
          => Tuple (AffinePoint (FVar f)) (AffinePoint (FVar f))
          -> Snarky (KimchiConstraint f) t Identity (AffinePoint (FVar f))
        circuit' = uncurry add_

        gen = do
          p1 <- genAffinePoint pg
          p2 <- genAffinePoint pg `suchThat` \p ->
            let
              { x: x1, y: y1 } = p1
              { x: x2, y: y2 } = p
            in
              x1 /= x2 && y1 /= negate y2
          pure $ Tuple p1 p2

      { builtState, solver } <- circuitTest' @f 100
        kimchiTestConfig
        ( NEA.singleton
            { testFunction: satisfied f
            , gen
            }
        )
        circuit'

      liftEffect $ verifyCircuit { s: builtState, gen, solver }
