module Snarky.Example.Types.SignedTransaction
  ( SignedTransaction(..)
  , signTransaction
  , verify
  ) where

import Prelude

import Data.Generic.Rep (class Generic)
import Data.Newtype (class Newtype)
import Data.Schnorr (Signature, sign)
import Data.Schnorr as Schnorr
import Data.Tuple.Nested (Tuple2, tuple2, uncurry2)
import Mina.ChainId (ChainId, networkId, signaturePrefix)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F(..), check, fieldsToValue, fieldsToVar, sizeInFields, valueToFields, varToFields)
import Snarky.Circuit.RandomOracle (toHashInput)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Types.PublicKey (PublicKey(..))
import Snarky.Example.Types.TokenAmount (TokenAmount)
import Snarky.Example.Types.Transaction (Transaction(..))
import Snarky.Example.Types.Transfer (Transfer(..))
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

signTransaction
  :: Pallas.ScalarField
  -> ChainId
  -> Transaction (F Vesta.ScalarField)
  -> Signature (F Vesta.ScalarField)
signTransaction privateKey chainId tx =
  let
    message = valueToFields tx
  in
    coerce $ sign
      { message
      , privateKey
      , networkId: networkId chainId
      , spongePrefix: signaturePrefix chainId
      }

verify
  :: ChainId
  -> SignedTransaction (F Vesta.ScalarField)
  -> Boolean
verify chainId (SignedTransaction { transaction, signature }) =
  let
    message = toHashInput transaction
    Transaction { transfer: Transfer { from: PublicKey from } } = transaction
  in
    Schnorr.verify (signaturePrefix chainId) (coerce signature) (coerce from) (coerce message :: Array Vesta.ScalarField)