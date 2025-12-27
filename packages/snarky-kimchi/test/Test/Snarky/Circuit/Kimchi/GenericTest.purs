module Test.Snarky.Circuit.Kimchi.GenericTest
  ( spec
  ) where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Either (Either(..))
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Effect.Class (liftEffect)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compilePure, makeSolver, runSolver)
import Snarky.Circuit.Curves (add_)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (AuxState(..), KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class WeierstrassCurve)
import Snarky.Data.EllipticCurve (AffinePoint, addAffine, genAffinePoint, toAffine)
import Test.QuickCheck (class Arbitrary, quickCheck')
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Test.Utils.Generic (class VerifyGeneric)
import Test.Utils.Generic as GenericUtils
import Type.Proxy (Proxy(..))

spec
  :: forall g f
   . KimchiConstraint.KimchiVerify f
  => Arbitrary g
  => WeierstrassCurve f g
  => VerifyGeneric f
  => Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec pg pc =
  describe "Kimchi Generic (EC Add)" do

    it "unsafeAdd Circuit generates valid Generic constraints" $ unsafePartial $
      let
        f (Tuple x y) = unsafePartial $ fromJust $ toAffine $ addAffine x y
        solver = makeSolver pc (uncurry add_)

        { constraints, aux: AuxState { wireState: { emittedRows, wireAssignments } } } =
          compilePure
            (Proxy @(Tuple (AffinePoint (F f)) (AffinePoint (F f))))
            (Proxy @(AffinePoint (F f)))
            pc
            (uncurry add_)
            Kimchi.initialState

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
        do
          circuitSpecPure' constraints KimchiConstraint.eval solver (satisfied f) gen
          liftEffect $ quickCheck' 10 do
            input <- gen
            let Right (Tuple _ varAssignments) = runSolver solver input
            pure $ GenericUtils.verify { wireAssignments, varAssignments, rows: emittedRows }

