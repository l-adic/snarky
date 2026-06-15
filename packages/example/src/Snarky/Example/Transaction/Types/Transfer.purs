module Snarky.Example.Transaction.Types.Transfer
  ( Transfer(..)
  ) where

import Prelude
import Simple.JSON (class ReadForeign, class WriteForeign)

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.RandomOracle (class Hashable)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
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
derive newtype instance WriteForeign f => WriteForeign (Transfer f)
derive newtype instance ReadForeign f => ReadForeign (Transfer f)
derive instance Eq f => Eq (Transfer f)
derive newtype instance (FieldSizeInBits f n, Compare 128 n LT, Arbitrary f) => Arbitrary (Transfer f)

instance CircuitType f (Transfer f) (Transfer (FVar f)) where
  sizeInFields pf _ =
    sizeInFields pf (Proxy @(Tuple3 (PublicKey f) (PublicKey f) (TokenAmount (F f))))
  valueToFields (Transfer t) = valueToFields (tuple3 t.from t.to (coerce t.amount :: TokenAmount (F f)))
  fieldsToValue fs =
    uncurry3 (\from to amount -> Transfer { from, to, amount: coerce amount })
      (fieldsToValue @_ @(Tuple3 (PublicKey f) (PublicKey f) (TokenAmount (F f))) fs)
  varToFields (Transfer t) =
    varToFields @_ @(Tuple3 (PublicKey f) (PublicKey f) (TokenAmount (F f)))
      (tuple3 t.from t.to t.amount)
  fieldsToVar fs =
    uncurry3 (\from to amount -> Transfer { from, to, amount })
      (fieldsToVar @_ @(Tuple3 (PublicKey f) (PublicKey f) (TokenAmount (F f))) fs)

instance
  ( CheckedType f c var
  , CheckedType f c (TokenAmount var)
  ) =>
  CheckedType f c (Transfer var) where
  check (Transfer t) = check (tuple3 t.from t.to t.amount)

-- | Flatten via the `CircuitType` field representation
-- | (`[ from.x, from.y, to.x, to.y, amount ]`).
instance Hashable (Transfer Vesta.ScalarField) Vesta.ScalarField where
  toHashInput = valueToFields

instance Hashable (Transfer Pallas.ScalarField) Pallas.ScalarField where
  toHashInput = valueToFields

instance Hashable (Transfer (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(Transfer f)