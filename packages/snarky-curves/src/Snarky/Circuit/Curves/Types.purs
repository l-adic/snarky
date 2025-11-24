module Snarky.Circuit.Curves.Types where

import Prelude

import Data.Maybe (fromJust, isJust)
import Partial.Unsafe (unsafePartial)
import Snarky.Circuit.Types (F(..))
import Snarky.Curves.Class (class WeierstrassCurve, toAffine)
import Test.QuickCheck (class Arbitrary, arbitrary)
import Test.QuickCheck.Gen (Gen, suchThat)
import Type.Proxy (Proxy)

type AffinePoint f = { x :: f, y :: f }

genAffinePoint
  :: forall g f
   . Arbitrary f
  => Arbitrary g
  => WeierstrassCurve f g
  => Proxy g
  -> Gen (AffinePoint (F f))
genAffinePoint _ = do
  mp <- (toAffine @f @g <$> arbitrary) `suchThat` isJust
  let { x, y } = unsafePartial $ fromJust mp
  pure { x: F x, y: F y }

type Point f = { x :: f, y :: f, z :: f }

type CurveParams f = { a :: f, b :: f }