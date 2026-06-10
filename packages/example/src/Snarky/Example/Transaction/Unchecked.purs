-- | Transaction operations over a ledger: constructing a signed transfer
-- | (`sign`) and applying one off-circuit (`applyTx`, the "arrow" between
-- | two ledgers).
-- |
-- | There is deliberately no hand-written value-level transfer logic here:
-- | `applyTx` *interprets* the checked circuit (`applyTxChecked`) on concrete
-- | values via `runAndCheck`, so the unchecked semantics cannot drift from
-- | what the snark proves. Anything `applyTx` accepts is by construction
-- | provable — and anything it rejects (bad signature, wrong nonce,
-- | overdraft, unknown account) would have been unprovable.
module Snarky.Example.Transaction.Unchecked
  ( sign
  , applyTx
  , touchedAccounts
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Sparse (Address)
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable)
import Data.Schnorr (toPublicKey)
import Data.Schnorr as Schnorr
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Effect.Ref as Ref
import Mina.ChainId (ChainId, networkId, signaturePrefix)
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Snarky.Backend.Compile (runAndCheck)
import Snarky.Circuit.DSL (const_, valueToFields)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Snarky.Example.Ledger (Ledger, lookupAddress)
import Snarky.Example.Transaction.Checked (applyTxChecked)
import Snarky.Example.Transaction.Monad (runTransferM)
import Snarky.Example.Transaction.Types (SignedTransaction(..), Transaction(..), Transfer(..))
import Snarky.Example.Types (PublicKey(..), TokenAmount)
import Type.Proxy (Proxy(..))

--------------------------------------------------------------------------------
-- Transaction construction

-- | Build and sign a transfer to `to` of `amount`, signed by `privateKey`
-- | (the signer's own key — the sender public key is derived from it as
-- | `[sk]·G`). `nonce` is the sender's current account nonce. Curve-bound by
-- | the Schnorr signature, hence pinned to `Vesta.ScalarField` / Pallas.
sign
  :: Pallas.ScalarField
  -> ChainId
  -> Vesta.ScalarField
  -> { amount :: TokenAmount Vesta.ScalarField
     , to :: PublicKey Vesta.ScalarField
     }
  -> SignedTransaction Vesta.ScalarField
sign privateKey chainId nonce txData =
  let
    fromPk = unsafePartial fromJust $ toAffine $ toPublicKey privateKey

    transaction :: Transaction Vesta.ScalarField
    transaction = Transaction
      { nonce
      , transfer: Transfer { from: PublicKey (coerce fromPk), to: txData.to, amount: txData.amount }
      }

    signature =
      Schnorr.sign
        { message: valueToFields transaction
        , privateKey
        , networkId: networkId chainId
        , spongePrefix: signaturePrefix chainId
        }
  in
    SignedTransaction
      { signature: coerce signature
      , transaction
      }

--------------------------------------------------------------------------------
-- The state transition

-- | The arrow between two ledgers: apply a signed transfer, returning the
-- | new ledger. This is the checked circuit run as the unchecked
-- | interpretation: `runAndCheck` computes every witness on concrete values
-- | and eagerly validates each assertion (signature verifies, sender owns the
-- | account, nonce matches, no under/overflow), throwing on the first
-- | violation. The `TransferM` advice monad serves the circuit's Merkle
-- | requests from — and applies its updates to — the ledger behind a local
-- | `Ref`; the mutated ledger is the result, and its root is the `target`
-- | digest of the corresponding base statement.
applyTx
  :: forall d
   . Reflectable d Int
  => ChainId
  -> SignedTransaction Vesta.ScalarField
  -> Ledger d
  -> Effect (Ledger d)
applyTx chainId tx ledger = do
  ref <- Ref.new ledger
  let
    Digest r = Sparse.root ledger.tree
    rootVar = Digest (const_ r)
  res <- runTransferM { currentTransaction: Nothing, ledger: ref } $
    runAndCheck
      (Proxy @(KimchiConstraint Vesta.ScalarField))
      (applyTxChecked @d chainId rootVar)
      tx
  case res of
    Left e -> throw $ "applyTx: invalid transaction: " <> show e
    Right (newRoot :: Digest Vesta.ScalarField) -> do
      ledger' <- Ref.read ref
      unless (Sparse.root ledger'.tree == newRoot) $
        throw "applyTx: ledger root does not match circuit output"
      pure ledger'

-- | The two account slots a transfer touches, for extracting a witness mask
-- | (`Mask.fromSubset`). Both accounts must already exist — there is no
-- | account creation (the circuit cannot prove it); an unknown key is simply
-- | omitted, and `applyTx` rejects the transaction before any snark work is
-- | created.
touchedAccounts
  :: forall d
   . Ledger d
  -> SignedTransaction Vesta.ScalarField
  -> Array (Tuple (Address d) (Maybe (PublicKey Vesta.ScalarField)))
touchedAccounts ledger transaction =
  let
    SignedTransaction { transaction: Transaction { transfer: Transfer { to, from } } } = transaction
  in
    Array.mapMaybe (\pk -> lookupAddress ledger pk <#> \addr -> Tuple addr (Just pk)) [ from, to ]
