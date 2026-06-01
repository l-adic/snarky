module Snarky.Example.Types.Account
  ( Account(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.MerkleTree.Hashable (class Hashable)
import Data.Newtype (class Newtype)
import Data.Tuple.Nested (Tuple3, tuple3, uncurry3)
import Prim.Int (class Compare)
import Prim.Ordering (LT)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Example.Types.PublicKey (PublicKey)
import Snarky.Example.Types.TokenAmount (TokenAmount)
import Test.QuickCheck (class Arbitrary)
import Type.Proxy (Proxy(..))

-- | Account type for merkle tree leaves
-- | Uses two field elements: publicKey and tokenBalance
newtype Account f = Account
  { publicKey :: PublicKey f
  , tokenBalance :: TokenAmount f
  , nonce :: f
  }

derive instance Newtype (Account f) _
derive instance Generic (Account f) _
derive newtype instance Show f => Show (Account f)
derive instance Eq f => Eq (Account f)
derive newtype instance (FieldSizeInBits f n, Compare 128 n LT, Arbitrary f) => Arbitrary (Account f)

-- | The `CircuitType`/`CheckedType` instances route through an explicit
-- | `Tuple3 (publicKey, tokenBalance, nonce)` rather than the record's
-- | RowList order, so the field layout is fixed and visible (pickles
-- | house style).
instance CircuitType f a var => CircuitType f (Account a) (Account var) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Tuple3 (PublicKey a) (TokenAmount a) a))
  valueToFields (Account acc) = valueToFields (tuple3 acc.publicKey acc.tokenBalance acc.nonce)
  fieldsToValue fs =
    uncurry3 (\publicKey tokenBalance nonce -> Account { publicKey, tokenBalance, nonce })
      (fieldsToValue @_ @(Tuple3 (PublicKey a) (TokenAmount a) a) fs)
  varToFields (Account acc) =
    varToFields @_ @(Tuple3 (PublicKey a) (TokenAmount a) a)
      (tuple3 acc.publicKey acc.tokenBalance acc.nonce)
  fieldsToVar fs =
    uncurry3 (\publicKey tokenBalance nonce -> Account { publicKey, tokenBalance, nonce })
      (fieldsToVar @_ @(Tuple3 (PublicKey a) (TokenAmount a) a) fs)

instance
  ( CheckedType f c var
  , CheckedType f c (TokenAmount var)
  ) =>
  CheckedType f c (Account var) where
  check (Account acc) = check (tuple3 acc.publicKey acc.tokenBalance acc.nonce)

-- | Flatten via the `CircuitType` field representation
-- | (`[ pk.x, pk.y, tokenBalance, nonce ]`); `MerkleHashable` — and hence
-- | the merkle leaf hash — is derived from this.
instance Hashable (Account (F f)) (F f) where
  toHashInput x = map F (valueToFields x)

instance Hashable (Account (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(Account (F f))
