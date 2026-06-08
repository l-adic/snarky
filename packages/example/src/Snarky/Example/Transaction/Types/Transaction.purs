module Snarky.Example.Transaction.Types.Transaction
  ( Transaction(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.RandomOracle (class Hashable)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Example.Transaction.Types.Transfer (Transfer)
import Snarky.Example.Types.TokenAmount (TokenAmount)
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

-- | A transaction: a `Transfer` plus a `nonce` (for replay protection).
-- | This — not the bare transfer — is the unit a sender signs.
newtype Transaction f = Transaction
  { nonce :: f
  , transfer :: Transfer f
  }

derive instance Newtype (Transaction f) _
derive instance Generic (Transaction f) _
derive newtype instance Show f => Show (Transaction f)
derive instance Eq f => Eq (Transaction f)
derive newtype instance (FieldSizeInBits f n, Compare 128 n LT, Arbitrary f) => Arbitrary (Transaction f)

instance
  CircuitType f a var =>
  CircuitType f (Transaction a) (Transaction var) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Tuple2 a (Transfer a)))
  valueToFields (Transaction t) = valueToFields (tuple2 t.nonce t.transfer)
  fieldsToValue fs =
    uncurry2 (\nonce transfer -> Transaction { nonce, transfer })
      (fieldsToValue @_ @(Tuple2 a (Transfer a)) fs)
  varToFields (Transaction t) =
    varToFields @_ @(Tuple2 a (Transfer a)) (tuple2 t.nonce t.transfer)
  fieldsToVar fs =
    uncurry2 (\nonce transfer -> Transaction { nonce, transfer })
      (fieldsToVar @_ @(Tuple2 a (Transfer a)) fs)

instance
  ( CheckedType f c var
  , CheckedType f c (TokenAmount var)
  ) =>
  CheckedType f c (Transaction var) where
  check (Transaction t) = check (tuple2 t.nonce t.transfer)

-- | Flatten via the `CircuitType` field representation
-- | (the nonce followed by the transfer's fields).
instance Hashable (Transaction (F f)) (F f) where
  toHashInput x = map F (valueToFields x)

instance Hashable (Transaction (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(Transaction (F f))