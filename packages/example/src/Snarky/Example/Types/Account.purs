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
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
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
-- | Value side is the raw field `f`. `publicKey` is already raw
-- | (`PublicKey f`); `tokenBalance` and the bare `nonce` leaf stay `F`-leaved
-- | in the routing tuple, so `coerce`/`F` bridge them at the seam.
instance CircuitType f (Account f) (Account (FVar f)) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Tuple3 (PublicKey f) (TokenAmount (F f)) (F f)))
  valueToFields (Account acc) =
    valueToFields (tuple3 acc.publicKey (coerce acc.tokenBalance :: TokenAmount (F f)) (F acc.nonce))
  fieldsToValue fs =
    uncurry3 (\pk tb n -> Account { publicKey: pk, tokenBalance: coerce tb, nonce: coerce n })
      (fieldsToValue @_ @(Tuple3 (PublicKey f) (TokenAmount (F f)) (F f)) fs)
  varToFields (Account acc) =
    varToFields @_ @(Tuple3 (PublicKey f) (TokenAmount (F f)) (F f))
      (tuple3 acc.publicKey acc.tokenBalance acc.nonce)
  fieldsToVar fs =
    uncurry3 (\publicKey tokenBalance nonce -> Account { publicKey, tokenBalance, nonce })
      (fieldsToVar @_ @(Tuple3 (PublicKey f) (TokenAmount (F f)) (F f)) fs)

instance
  ( CheckedType f c var
  , CheckedType f c (TokenAmount var)
  ) =>
  CheckedType f c (Account var) where
  check (Account acc) = check (tuple3 acc.publicKey acc.tokenBalance acc.nonce)

-- | Flatten via the `CircuitType` field representation
-- | (`[ pk.x, pk.y, tokenBalance, nonce ]`); `MerkleHashable` — and hence
-- | the merkle leaf hash — is derived from this.
-- | Concrete value-side instances (not a generic `Hashable (Account f) f`,
-- | which would overlap the `FVar` instance when `f = FVar _`).
instance Hashable (Account Vesta.ScalarField) Vesta.ScalarField where
  toHashInput = valueToFields

instance Hashable (Account Pallas.ScalarField) Pallas.ScalarField where
  toHashInput = valueToFields

instance Hashable (Account (FVar f)) (FVar f) where
  toHashInput = varToFields @_ @(Account f)
