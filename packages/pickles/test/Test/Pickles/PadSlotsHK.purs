-- | Smoke tests for `Pickles.Wrap.Slots.PadSlots` — the production
-- | class used by `wrapMain` for structural traversal over slot
-- | lists. Each test exercises the class via the `NoSlots` /
-- | `Slots1` / `Slots2` type synonyms + smart constructors that the
-- | library exports.
-- |
-- | The class, instances, type synonyms, and smart constructors all
-- | live in `Pickles.Wrap.Slots`. This test module only verifies
-- | that the class methods produce the expected runtime values for
-- | concrete slot shapes.
module Test.Pickles.PadSlotsHK
  ( spec
  ) where

import Prelude

import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Types (PaddedLength)
import Pickles.Wrap.Slots (NoSlots, Slots1, Slots2, noSlots, padAllSlots, slots1, slots2, slotWidthsOf)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

spec :: Spec Unit
spec = describe "Pickles.Wrap.Slots.PadSlots" do
  it "NoSlots (mpv=0): produces empty vectors" do
    let
      widths :: Vector 0 Int
      widths = slotWidthsOf (Proxy :: Proxy NoSlots)

      padded :: Vector 0 (Vector PaddedLength Int)
      padded = padAllSlots 99 (noSlots :: NoSlots Int)
    toArr widths `shouldEqual` []
    map toArr (toArr padded) `shouldEqual` []

  it "Slots1 0: one slot of width 0" do
    let
      tup :: Slots1 0 Int
      tup = slots1 Vector.nil

      widths :: Vector 1 Int
      widths = slotWidthsOf (Proxy :: Proxy (Slots1 0))

      padded :: Vector 1 (Vector PaddedLength Int)
      padded = padAllSlots 99 tup
    toArr widths `shouldEqual` [ 0 ]
    map toArr (toArr padded) `shouldEqual` [ [ 99, 99 ] ]

  it "Slots1 1: one slot with one real entry" do
    let
      tup :: Slots1 1 Int
      tup = slots1 (42 :< Vector.nil)

      widths :: Vector 1 Int
      widths = slotWidthsOf (Proxy :: Proxy (Slots1 1))

      padded :: Vector 1 (Vector PaddedLength Int)
      padded = padAllSlots 99 tup
    toArr widths `shouldEqual` [ 1 ]
    map toArr (toArr padded) `shouldEqual` [ [ 99, 42 ] ]

  it "Slots2 0 1: two slots of different widths" do
    let
      tup :: Slots2 0 1 Int
      tup = slots2 Vector.nil (7 :< Vector.nil)

      widths :: Vector 2 Int
      widths = slotWidthsOf (Proxy :: Proxy (Slots2 0 1))

      padded :: Vector 2 (Vector PaddedLength Int)
      padded = padAllSlots 99 tup
    toArr widths `shouldEqual` [ 0, 1 ]
    map toArr (toArr padded) `shouldEqual`
      [ [ 99, 99 ], [ 99, 7 ] ]

  it "Slots2 2 2: two full-width slots" do
    let
      tup :: Slots2 2 2 Int
      tup = slots2 (1 :< 2 :< Vector.nil) (3 :< 4 :< Vector.nil)

      widths :: Vector 2 Int
      widths = slotWidthsOf (Proxy :: Proxy (Slots2 2 2))

      padded :: Vector 2 (Vector PaddedLength Int)
      padded = padAllSlots 99 tup
    toArr widths `shouldEqual` [ 2, 2 ]
    map toArr (toArr padded) `shouldEqual`
      [ [ 1, 2 ], [ 3, 4 ] ]
  where
  toArr :: forall n a. Vector n a -> Array a
  toArr = Vector.toUnfoldable
