{-
Variant C — IntEq(len, mpvMax)-based dispatch, per expert suggestion.
Dispatches on whether len == mpvMax (always concrete at use sites)
rather than IsZero(mpvPad) (unknown in case 3).
Goal: all three probes typecheck simultaneously.
-}
module Test.Pickles.MpvPaddingProbe where

import Prelude

import Data.Reflectable (class Reflectable)
import Prim.Boolean (False, True)
import Prim.Int (class Add)

class IntEq (a :: Int) (b :: Int) (res :: Boolean) | a b -> res

instance IntEq a a True
else instance IntEq a b False

class MpvPaddingDispatch (isEqual :: Boolean) (mpvPad :: Int) (len :: Int) (mpvMax :: Int)
   | isEqual mpvPad len -> mpvMax
   , isEqual len mpvMax -> mpvPad
   , isEqual mpvPad mpvMax -> len

instance MpvPaddingDispatch True 0 len len
instance Add mpvPad len mpvMax => MpvPaddingDispatch False mpvPad len mpvMax

class MpvPadding (mpvPad :: Int) (len :: Int) (mpvMax :: Int)
   | mpvPad len -> mpvMax
   , len mpvMax -> mpvPad
   , mpvPad mpvMax -> len

instance
  ( IntEq len mpvMax isEqual
  , MpvPaddingDispatch isEqual mpvPad len mpvMax
  ) =>
  MpvPadding mpvPad len mpvMax

discharge
  :: forall @mpvPad @len @mpvMax
   . MpvPadding mpvPad len mpvMax
  => Unit
discharge = unit

withLenMpvMax
  :: forall @len @mpvMax mpvPad
   . MpvPadding mpvPad len mpvMax
  => Reflectable mpvPad Int
  => Unit
withLenMpvMax = unit

probe1Abstract :: forall a. Unit
probe1Abstract = discharge @0 @a @a

probe2Concrete :: Unit
probe2Concrete = discharge @1 @0 @1

probe3FunDepDerive :: Unit
probe3FunDepDerive = withLenMpvMax @1 @1
