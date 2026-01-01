module Test.Snarky.Circuit.Kimchi.GenericTest
  ( spec
  ) where

import Prelude

import Control.Monad.Gen (suchThat)
import Data.Maybe (fromJust)
import Data.Tuple (Tuple(..), uncurry)
import Partial.Unsafe (unsafePartial)
import Snarky.Backend.Compile (compilePure, makeSolver)
import Snarky.Circuit.Curves (add_)
import Snarky.Circuit.Types (F)
import Snarky.Constraint.Kimchi (class KimchiVerify, KimchiConstraint)
import Snarky.Constraint.Kimchi as Kimchi
import Snarky.Constraint.Kimchi as KimchiConstraint
import Snarky.Curves.Class (class WeierstrassCurve)
import Snarky.Data.EllipticCurve (AffinePoint, addAffine, genAffinePoint, toAffine)
import Test.QuickCheck (class Arbitrary)
import Test.Snarky.Circuit.Utils (circuitSpecPure', satisfied)
import Test.Spec (Spec, describe, it)
import Type.Proxy (Proxy(..))

spec
  :: forall g f f'
   . KimchiConstraint.KimchiVerify f f'
  => Arbitrary g
  => WeierstrassCurve f g
  => KimchiVerify f f'
  => Proxy g
  -> Proxy (KimchiConstraint f)
  -> Spec Unit
spec pg pc =
  describe "Kimchi Generic (EC Add)" do

    it "unsafeAdd Circuit generates valid Generic constraints" $ unsafePartial $
      let
        f (Tuple x y) = unsafePartial $ fromJust $ toAffine $ addAffine x y
        solver = makeSolver pc (uncurry add_)

        { constraints } =
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