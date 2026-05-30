module Snarky.Example.Circuits
  ( class AccountMapM
  , getAccountId
  , class TransactionM
  , getCurrentTransaction
  , processTransaction
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.MerkleTree.Hashable (toHashInput)
import Data.MerkleTree.Sized (Address)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Data.Schnorr (Signature(..)) as Schnorr
import Mina.ChainId (ChainId, signaturePrefix)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, add_, assertEq, assert_, const_, exists, not_, read, unpack_)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Circuit.Schnorr (Signature(..), verifies)
import Snarky.Circuit.Schnorr.Shifted as Shifted
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Types (Account(..), PublicKey(..), SignedTransaction(..), Transaction(..), Transfer(..), addWithOverflow, subWithUnderflow)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- | Advice monad for looking up account addresses from public keys.
-- |
-- | This typeclass allows circuits to "conjure" an address from a public key
-- | during witness generation. The prover provides the mapping externally.
class Monad m <= AccountMapM m f (d :: Int) | m -> f d where
  getAccountId :: PublicKey (F f) -> m (Address d)

--------------------------------------------------------------------------------
-- | Advice monad for supplying the transaction being proven as a private
-- | witness. The pickled {source, target} statement does not carry the
-- | `SignedTransaction`; the prover conjures it in-circuit via `exists`,
-- | reading it from the witness monad's own instance.
class Monad m <= TransactionM m f | m -> f where
  getCurrentTransaction :: m (SignedTransaction (F f))

--------------------------------------------------------------------------------

-- | Transfer tokens between accounts.
-- |
-- | This circuit:
-- | 1. Takes a transaction (public keys + amount)
-- | 2. Looks up addresses from public keys via AccountMapM
-- | 3. Fetches sender account, verifies ownership, debits the amount
-- | 4. Fetches receiver account, verifies ownership, credits the amount
-- | 5. Returns the new merkle root
-- |
-- | Note: Addresses are assigned sequentially in Mina (not derived from public keys).
-- | The circuit verifies the account at each address has the expected public key.
processTransaction
  :: forall t m @d
   . Reflectable d Int
  => AccountMapM m Vesta.ScalarField d
  => CMT.MerkleRequestM m Vesta.ScalarField (Account (F Vesta.ScalarField)) d (Account (FVar Vesta.ScalarField))
  => CircuitM Vesta.ScalarField (KimchiConstraint Vesta.ScalarField) t m
  => ChainId
  -> Digest (FVar Vesta.ScalarField)
  -> SignedTransaction (FVar Vesta.ScalarField)
  -> Snarky (KimchiConstraint Vesta.ScalarField) t m (Digest (FVar Vesta.ScalarField))
processTransaction chainId root (SignedTransaction { signature, transaction }) = do
  let
    Transaction { nonce, transfer: Transfer { from, to, amount } } = transaction
    Schnorr.Signature { r, s } = signature
  -- Verify the sender's signature over the transaction in-circuit. The
  -- pure signature carries `s` as a field; unpack it into the 255-bit
  -- form the circuit verifier consumes.

  signatureVerifies <- do
    sBits <- unpack_ s (Proxy @255)
    scalarOps <- Shifted.pallasScalarOps
    verifies (signaturePrefix chainId) scalarOps
      { publicKey: un PublicKey from
      , signature: Signature { r, s: sBits }
      , message: toHashInput transaction
      }
  assert_ signatureVerifies

  -- Debit sender: verify ownership and subtract amount
  { root: root' } <- do
    fromAddr <- exists do
      fromPk <- read from
      lift $ getAccountId fromPk
    CMT.fetchAndUpdate fromAddr root \(Account acc) -> do
      -- Verify sender owns this account
      assertEq acc.publicKey from
      assertEq acc.nonce nonce
      -- Debit the amount
      { result: newBalance, underflow } <- acc.tokenBalance `subWithUnderflow` amount
      assert_ (not_ underflow)
      pure $ Account acc { tokenBalance = newBalance, nonce = add_ nonce (const_ one) }

  -- Credit receiver: verify ownership and add amount
  { root: root'' } <- do
    toAddr <- exists do
      toPk <- read to
      lift $ getAccountId toPk

    CMT.fetchAndUpdate toAddr root' \(Account acc) -> do
      -- Verify receiver owns this account
      assertEq acc.publicKey to
      -- Credit the amount
      { result: newBalance, overflow } <- acc.tokenBalance `addWithOverflow` amount
      assert_ (not_ overflow)
      pure $ Account acc { tokenBalance = newBalance }

  pure root''