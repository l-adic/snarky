module Snarky.Example.Transaction.Types.Transfer
  ( Transfer(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.RandomOracle (class Hashable)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Example.Types.PublicKey (PublicKey)
import Snarky.Example.Types.TokenAmount (TokenAmount)
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

-- | Transfer representing a transfer between accounts. Specifies the
-- | public keys and amount; addresses are an internal detail the prover
-- | looks up from the account map.
-- |
-- | A newtype (not a type alias) so it can carry instances — in
-- | particular `CircuitType`, whose `valueToFields` yields the
-- | `Array f` field representation (`[from, to, amount]`).
newtype Transfer f = Transfer
  { from :: PublicKey f
  , to :: PublicKey f
  , amount :: TokenAmount f
  }

derive instance Newtype (Transfer f) _
derive instance Generic (Transfer f) _
derive newtype instance Show f => Show (Transfer f)
derive instance Eq f => Eq (Transfer f)
derive newtype instance (FieldSizeInBits f n, Compare 128 n LT, Arbitrary f) => Arbitrary (Transfer f)

instance
  ( CircuitType f a var
  ) =>
  CircuitType f (Transfer a) (Transfer var) where
  sizeInFields pf _ =
    sizeInFields pf (Proxy @(Tuple3 (PublicKey a) (PublicKey a) (TokenAmount a)))
  valueToFields (Transfer t) = valueToFields (tuple3 t.from t.to t.amount)
  fieldsToValue fs =
    uncurry3 (\from to amount -> Transfer { from, to, amount })
      (fieldsToValue @_ @(Tuple3 (PublicKey a) (PublicKey a) (TokenAmount a)) fs)
  varToFields (Transfer t) =
    varToFields @_ @(Tuple3 (PublicKey a) (PublicKey a) (TokenAmount a))
      (tuple3 t.from t.to t.amount)
  fieldsToVar fs =
    uncurry3 (\from to amount -> Transfer { from, to, amount })
      (fieldsToVar @_ @(Tuple3 (PublicKey a) (PublicKey a) (TokenAmount a)) fs)

instance
  ( CheckedType f c var
  , CheckedType f c (TokenAmount var)
  ) =>
  CheckedType f c (Transfer var) where
  check (Transfer t) = check (tuple3 t.from t.to t.amount)

-- | Flatten via the `CircuitType` field representation
-- | (`[ from.x, from.y, to.x, to.y, amount ]`).
instance Hashable (Transfer (F f)) (F f) where
  toHashInput x = map F (valueToFields x)

instance Hashable (Transfer (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(Transfer (F f))