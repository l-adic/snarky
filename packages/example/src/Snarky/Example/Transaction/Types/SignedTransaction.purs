module Snarky.Example.Transaction.Types.SignedTransaction
  ( SignedTransaction(..)
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Schnorr (Signature)
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
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
derive instance Eq f => Eq (SignedTransaction f)

instance CircuitType f a var => CircuitType f (SignedTransaction a) (SignedTransaction var) where
  sizeInFields pf _ = sizeInFields pf (Proxy @(Tuple2 (Signature a) (Transaction a)))
  valueToFields (SignedTransaction st) = valueToFields (tuple2 st.signature st.transaction)
  fieldsToValue fs =
    uncurry2 (\signature transaction -> SignedTransaction { signature, transaction })
      (fieldsToValue @_ @(Tuple2 (Signature a) (Transaction a)) fs)
  varToFields (SignedTransaction st) =
    varToFields @_ @(Tuple2 (Signature a) (Transaction a))
      (tuple2 st.signature st.transaction)
  fieldsToVar fs =
    uncurry2 (\signature transaction -> SignedTransaction { signature, transaction })
      (fieldsToVar @_ @(Tuple2 (Signature a) (Transaction a)) fs)

instance
  ( CheckedType f c var
  , CheckedType f c (TokenAmount var)
  ) =>
  CheckedType f c (SignedTransaction var) where
  check (SignedTransaction st) = check (tuple2 st.signature st.transaction)