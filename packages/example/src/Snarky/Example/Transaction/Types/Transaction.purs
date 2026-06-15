module Snarky.Example.Transaction.Types.Transaction
  ( Transaction(..)
  ) where

import Prelude
import Simple.JSON (class ReadForeign, class WriteForeign)

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.RandomOracle (class Hashable)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
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
derive newtype instance WriteForeign f => WriteForeign (Transaction f)
derive newtype instance ReadForeign f => ReadForeign (Transaction f)
derive instance Eq f => Eq (Transaction f)
derive newtype instance (FieldSizeInBits f n, Compare 128 n LT, Arbitrary f) => Arbitrary (Transaction f)

instance CircuitType f (Transaction f) (Transaction (FVar f)) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Tuple2 (F f) (Transfer f)))
  valueToFields (Transaction t) = valueToFields (tuple2 (F t.nonce) t.transfer)
  fieldsToValue fs =
    uncurry2 (\nonce transfer -> Transaction { nonce: coerce nonce, transfer })
      (fieldsToValue @_ @(Tuple2 (F f) (Transfer f)) fs)
  varToFields (Transaction t) =
    varToFields @_ @(Tuple2 (F f) (Transfer f)) (tuple2 t.nonce t.transfer)
  fieldsToVar fs =
    uncurry2 (\nonce transfer -> Transaction { nonce, transfer })
      (fieldsToVar @_ @(Tuple2 (F f) (Transfer f)) fs)

instance
  ( CheckedType f c var
  , CheckedType f c (TokenAmount var)
  ) =>
  CheckedType f c (Transaction var) where
  check (Transaction t) = check (tuple2 t.nonce t.transfer)

-- | Flatten via the `CircuitType` field representation
-- | (the nonce followed by the transfer's fields).
instance Hashable (Transaction Vesta.ScalarField) Vesta.ScalarField where
  toHashInput = valueToFields

instance Hashable (Transaction Pallas.ScalarField) Pallas.ScalarField where
  toHashInput = valueToFields

instance Hashable (Transaction (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(Transaction f)