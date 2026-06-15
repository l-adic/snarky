module Snarky.Example.Transaction.Types.SignedTransaction
  ( SignedTransaction(..)
  ) where

import Prelude
import Simple.JSON (class ReadForeign, class WriteForeign)

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Schnorr (Signature)
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), FVar, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Example.Transaction.Types.Transaction (Transaction)
import Snarky.Example.Types.TokenAmount (TokenAmount)
import Type.Proxy (Proxy(..))

-- | A transaction together with a Schnorr signature over it. This is
-- | what a sender submits; the prover verifies the signature against the
-- | sender's public key before applying the transfer.
newtype SignedTransaction f = SignedTransaction
  { signature :: Signature f
  , transaction :: Transaction f
  }

derive instance Newtype (SignedTransaction f) _
derive instance Generic (SignedTransaction f) _
derive newtype instance Show f => Show (SignedTransaction f)
derive newtype instance WriteForeign f => WriteForeign (SignedTransaction f)
derive newtype instance ReadForeign f => ReadForeign (SignedTransaction f)
derive instance Eq f => Eq (SignedTransaction f)

instance CircuitType f (SignedTransaction f) (SignedTransaction (FVar f)) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Tuple2 (Signature (F f)) (Transaction f)))
  valueToFields (SignedTransaction st) = valueToFields (tuple2 (coerce st.signature :: Signature (F f)) st.transaction)
  fieldsToValue fs =
    uncurry2 (\signature transaction -> SignedTransaction { signature: coerce signature, transaction })
      (fieldsToValue @_ @(Tuple2 (Signature (F f)) (Transaction f)) fs)
  varToFields (SignedTransaction st) =
    varToFields @_ @(Tuple2 (Signature (F f)) (Transaction f))
      (tuple2 st.signature st.transaction)
  fieldsToVar fs =
    uncurry2 (\signature transaction -> SignedTransaction { signature, transaction })
      (fieldsToVar @_ @(Tuple2 (Signature (F f)) (Transaction f)) fs)

instance
  ( CheckedType f c var
  , CheckedType f c (TokenAmount var)
  ) =>
  CheckedType f c (SignedTransaction var) where
  check (SignedTransaction st) = check (tuple2 st.signature st.transaction)