module Pickles.Types
  ( OtherField
  , SplitField
  , class HasOtherField
  , toOtherField
  , fromOtherField
  ) where

import Prelude

import JS.BigInt as BigInt
import Snarky.Circuit.Types (F(..))
import Snarky.Curves.Class (fromBigInt, toBigInt)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Types.Shifted (class Shifted, Type1)

newtype OtherField f = OtherField f

derive instance Eq f => Eq (OtherField f)
derive newtype instance Show f => Show (OtherField f)

data SplitField f b = SplitField f b

derive instance (Eq f, Eq b) => Eq (SplitField f b)
instance (Show f, Show b) => Show (SplitField f b) where
  show (SplitField f b) = "SplitField " <> show f <> " " <> show b

class HasOtherField f f' where
  toOtherField :: f -> f'
  fromOtherField :: f' -> f

-- | Pallas.ScalarField (Fq) is larger than Vesta.ScalarField (Fp)
-- | so we need to split it into (sDiv2, sOdd) where s = 2*sDiv2 + sOdd
instance HasOtherField Pallas.ScalarField (SplitField Vesta.ScalarField Boolean) where
  toOtherField s =
    let
      sBigInt = toBigInt s
      sOdd = BigInt.odd sBigInt
      sDiv2BigInt = (sBigInt - (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)) / BigInt.fromInt 2
    in
      SplitField (fromBigInt sDiv2BigInt) sOdd

  fromOtherField (SplitField sDiv2 sOdd) =
    let
      sDiv2BigInt = toBigInt sDiv2
      sBigInt = BigInt.fromInt 2 * sDiv2BigInt + (if sOdd then BigInt.fromInt 1 else BigInt.fromInt 0)
    in
      fromBigInt sBigInt

-- | Vesta.ScalarField (Fp) fits directly in Pallas.ScalarField (Fq)
-- | so we can convert via BigInt
instance HasOtherField Vesta.ScalarField (OtherField Pallas.ScalarField) where
  toOtherField s = OtherField (fromBigInt (toBigInt s))
  fromOtherField (OtherField s) = fromBigInt (toBigInt s)

instance HasOtherField f (SplitField f' b) => HasOtherField (F f) (SplitField (F f') b) where
  toOtherField (F f) =
    let
      SplitField f' b = toOtherField f
    in
      SplitField (F f') b
  fromOtherField (SplitField (F f') b) = F $ fromOtherField $ SplitField f' b

instance HasOtherField f (OtherField f') => HasOtherField (F f) (OtherField (F f')) where
  toOtherField (F f) =
    let
      OtherField f' = toOtherField f
    in
      OtherField (F f')
  fromOtherField (OtherField (F f')) = F $ fromOtherField $ OtherField f'