-- | De-risking experiment 1b (revised): higher-kinded slot list
-- | built from the **existing** functor combinators in
-- | `Data.Functor.Product` and `Data.Const`, no custom data types
-- | and no custom infix operator.
-- |
-- | The slot list is a nested `Product` of `Vector w` shape
-- | constructors, terminated by `Const Unit` (the functor that
-- | ignores its element type and carries zero content).
-- |
-- | @
-- |   -- Type-level spec: two slots of widths 0 and 1
-- |   type S = Product (Vector 0) (Product (Vector 1) (Const Unit))
-- |
-- |   -- Value-level: `product` constructs the nested pair;
-- |   -- `Const unit` is the nil terminator.
-- |   s :: S Int
-- |   s = product Vector.nil
-- |         (product (7 :< Vector.nil) (Const unit))
-- | @
-- |
-- | The class `PadSlots` has a higher-kinded `slots :: Type -> Type`
-- | parameter and inducts over the `Product` / `Const Unit`
-- | structure via two instances. Since we're using standard library
-- | types, the existing `Newtype` / `Functor` / etc. instances are
-- | all available for free.
module Test.Pickles.PadSlotsHK
  ( spec
  ) where

import Prelude

import Data.Const (Const(..))
import Data.Functor.Product (Product, product)
import Data.Newtype (unwrap)
import Data.Reflectable (class Reflectable, reflectType)
import Data.Tuple (Tuple(..))
import Data.Vector (Vector, (:<))
import Data.Vector as Vector
import Pickles.Types (PaddedLength)
import Prim.Int (class Add)
import Test.Spec (Spec, describe, it)
import Test.Spec.Assertions (shouldEqual)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Class with higher-kinded `slots :: Type -> Type`.
--
-- `a` is method-level `forall`, never a class parameter. The fundep
-- `| slots -> mpv` is the only dependency needed — no redundant `a`
-- at the class level.
--------------------------------------------------------------------------------

class PadSlots (slots :: Type -> Type) (mpv :: Int) | slots -> mpv where
  slotWidthsOf :: Proxy slots -> Vector mpv Int
  padAllSlots :: forall a. a -> slots a -> Vector mpv (Vector PaddedLength a)

-- Nil case: `Const Unit` is the "empty slot list" — a functor that
-- ignores its element type and carries a single `Unit` value.
-- `Const Unit a = Const unit` for any `a`, so no `a` appears on the
-- RHS of the instance. mpv=0.
instance PadSlots (Const Unit) 0 where
  slotWidthsOf _ = Vector.nil
  padAllSlots _ _ = Vector.nil

-- Cons case: `Product (Vector w) rest` — a Vector of width `w`
-- paired pointwise with the tail `rest :: Type -> Type`.
--
-- Pattern-matching on the `Product` newtype gives us the head
-- `Vector w a` and the tail `rest a`, both sharing the same element
-- type `a` (this is the functor product's correctness invariant).
instance
  ( Reflectable w Int
  , Add pad w PaddedLength
  , Reflectable pad Int
  , PadSlots rest restLen
  , Add restLen 1 mpv
  , Reflectable mpv Int
  ) =>
  PadSlots (Product (Vector w) rest) mpv where
  slotWidthsOf _ =
    reflectType (Proxy :: Proxy w) :< slotWidthsOf (Proxy :: Proxy rest)
  padAllSlots dummy p =
    let
      Tuple headSlot restSlot = unwrap p
    in
      padSlotDummy dummy headSlot :< padAllSlots dummy restSlot

-- | Stand-in for `Wrap.Main.padWrapChallenges`.
padSlotDummy
  :: forall w pad a
   . Reflectable pad Int
  => Add pad w PaddedLength
  => a
  -> Vector w a
  -> Vector PaddedLength a
padSlotDummy dummy slot =
  let
    padding :: Vector pad a
    padding = Vector.replicate dummy
  in
    Vector.append padding slot

--------------------------------------------------------------------------------
-- Smoke spec — exercise all mpv values (0, 1, 2) through a single class.
--------------------------------------------------------------------------------

spec :: Spec Unit
spec = describe "PadSlotsHK (Product/Const slot list)" do
  it "mpv=0: Const Unit nil produces empty vectors" do
    let
      widths :: Vector 0 Int
      widths = slotWidthsOf (Proxy :: Proxy (Const Unit))

      padded :: Vector 0 (Vector PaddedLength Int)
      padded = padAllSlots 99 (Const unit :: Const Unit Int)
    toArr widths `shouldEqual` []
    map toArr (toArr padded) `shouldEqual` []

  it "mpv=1, slotWidth=0: one slot of width 0" do
    let
      slot :: Vector 0 Int
      slot = Vector.nil

      tup :: Product (Vector 0) (Const Unit) Int
      tup = product slot (Const unit)

      widths :: Vector 1 Int
      widths = slotWidthsOf (Proxy :: Proxy (Product (Vector 0) (Const Unit)))

      padded :: Vector 1 (Vector PaddedLength Int)
      padded = padAllSlots 99 tup
    toArr widths `shouldEqual` [ 0 ]
    map toArr (toArr padded) `shouldEqual` [ [ 99, 99 ] ]

  it "mpv=1, slotWidth=1: one slot of width 1" do
    let
      slot :: Vector 1 Int
      slot = 42 :< Vector.nil

      tup :: Product (Vector 1) (Const Unit) Int
      tup = product slot (Const unit)

      widths :: Vector 1 Int
      widths = slotWidthsOf (Proxy :: Proxy (Product (Vector 1) (Const Unit)))

      padded :: Vector 1 (Vector PaddedLength Int)
      padded = padAllSlots 99 tup
    toArr widths `shouldEqual` [ 1 ]
    map toArr (toArr padded) `shouldEqual` [ [ 99, 42 ] ]

  it "mpv=2, slot widths (0, 1)" do
    let
      slot0 :: Vector 0 Int
      slot0 = Vector.nil

      slot1 :: Vector 1 Int
      slot1 = 7 :< Vector.nil

      tup :: Product (Vector 0) (Product (Vector 1) (Const Unit)) Int
      tup = product slot0 (product slot1 (Const unit))

      widths :: Vector 2 Int
      widths = slotWidthsOf
        (Proxy :: Proxy (Product (Vector 0) (Product (Vector 1) (Const Unit))))

      padded :: Vector 2 (Vector PaddedLength Int)
      padded = padAllSlots 99 tup
    toArr widths `shouldEqual` [ 0, 1 ]
    map toArr (toArr padded) `shouldEqual`
      [ [ 99, 99 ], [ 99, 7 ] ]

  it "mpv=2, slot widths (2, 2)" do
    let
      slot0 :: Vector 2 Int
      slot0 = 1 :< 2 :< Vector.nil

      slot1 :: Vector 2 Int
      slot1 = 3 :< 4 :< Vector.nil

      tup :: Product (Vector 2) (Product (Vector 2) (Const Unit)) Int
      tup = product slot0 (product slot1 (Const unit))

      widths :: Vector 2 Int
      widths = slotWidthsOf
        (Proxy :: Proxy (Product (Vector 2) (Product (Vector 2) (Const Unit))))

      padded :: Vector 2 (Vector PaddedLength Int)
      padded = padAllSlots 99 tup
    toArr widths `shouldEqual` [ 2, 2 ]
    map toArr (toArr padded) `shouldEqual`
      [ [ 1, 2 ], [ 3, 4 ] ]
  where
  toArr :: forall n a. Vector n a -> Array a
  toArr = Vector.toUnfoldable
