-- | Transaction operations over a ledger: constructing a signed transfer
-- | (`sign`) and applying one off-circuit (`apply`, the
-- | "arrow" between two ledgers). The prover-side advice monad these run
-- | alongside — and the `TransactionM` advice class — live in
-- | `Snarky.Example.Transaction.Monad`.
module Snarky.Example.Transaction.Unchecked
  ( sign
  , applyTx
  , touchedAccounts
  ) where

import Prelude

import Data.Array as Array
import Data.Foldable (foldl)
import Data.Map as Map
import Data.Maybe (Maybe(..), fromJust)
import Data.MerkleTree.Hashable (toHashInput)
import Data.MerkleTree.Sparse (Address(..))
import Data.MerkleTree.Sparse as Sparse
import Data.Reflectable (class Reflectable)
import Data.Schnorr (toPublicKey)
import Data.Schnorr as Schnorr
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Mina.ChainId (ChainId, networkId, signaturePrefix)
import Partial.Unsafe (unsafePartial)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (valueToFields)
import Snarky.Curves.Class (toAffine)
import Snarky.Curves.Pallas as Pallas
import Snarky.Curves.Vesta as Vesta
import Snarky.Data.EllipticCurve (AffinePoint(..))
import Snarky.Example.Ledger (Ledger, balanceOf, getAccount, lookupAddress)
import Snarky.Example.Transaction.Types (SignedTransaction(..), Transaction(..), Transfer(..))
import Snarky.Example.Types (Account(..), PublicKey(..), TokenAmount, mkAmount)
import Snarky.Example.Types.Account as Account

--------------------------------------------------------------------------------
-- Transaction construction

verifySignature
  :: ChainId
  -> SignedTransaction Vesta.ScalarField
  -> Boolean
verifySignature chainId (SignedTransaction { transaction, signature }) =
  let
    message = toHashInput transaction
    Transaction { transfer: Transfer { from: PublicKey from } } = transaction
  in
    Schnorr.verify (signaturePrefix chainId) (coerce signature) (coerce from) (coerce message :: Array Vesta.ScalarField)

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
-- | new ledger. Debits the sender (and bumps its nonce) and credits the
-- | receiver. This is the pure mirror of the in-circuit `processTransaction`
-- | (the `Test.Snarky.Example.Circuits` quickcheck spec checks they agree),
-- | and the resulting tree's root is the `target` ledger digest of the
-- | corresponding base statement.
applyTx
  :: forall d
   . Reflectable d Int
  => ChainId
  -> SignedTransaction Vesta.ScalarField
  -> Ledger d Vesta.ScalarField
  -> Effect (Ledger d Vesta.ScalarField)
applyTx chainId tx ledger = do
  let
    SignedTransaction { transaction: Transaction { transfer: Transfer { from, to, amount } } } = tx
    amt = balanceOf amount

  unless (verifySignature chainId tx) $
    throw "Invalid signature on transaction"

  ledger' <- do
    fromAddr <- case lookupAddress ledger from of
      Just a -> pure a
      Nothing -> throw $ "Missing address for public key " <> show from
    Account account <- case getAccount ledger fromAddr of
      Just a -> pure a
      Nothing -> throw $ "Missing account for public key " <> show from
    newBalance <- case mkAmount (balanceOf account.tokenBalance - amt) of
      Just b -> pure b
      Nothing -> throw $ "Send amount exceeded account balance"
    let
      -- debit the transfer amount from the sender
      account' = Account account
        { tokenBalance = newBalance
        , nonce = account.nonce + one
        }
      tree' = unsafePartial fromJust $ Sparse.set fromAddr account' ledger.tree
    pure ledger { tree = tree' }

  ledger'' <- do
    res <- case lookupAddress ledger' to of
      -- if the account already exists, just return it
      Just address -> do
        case getAccount ledger' address of
          Just account -> pure { account, address, ledger: ledger' }
          Nothing -> throw $ "Missing account for public key " <> show to
      -- otherwise create a blank account for this pub key and return it
      Nothing -> do
        let
          address = Sparse.Address ledger'.nextAddress
          account = Account.default to
        case Sparse.set address account ledger'.tree of
          Nothing -> throw "Exceeded ledger max size"
          Just tree' -> do
            let
              ledger'' = ledger'
                { tree = tree'
                , accountMap = Map.insert to address ledger'.accountMap
                , nextAddress = ledger'.nextAddress + one
                }
            pure { account, address, ledger: ledger'' }
    let
      -- add the transfer amount to the recipient
      Account account = res.account
      newBalance = unsafePartial fromJust $ mkAmount (balanceOf account.tokenBalance + amt)
      account' = Account account
        { tokenBalance = newBalance
        }
    pure res.ledger { tree = unsafePartial $ fromJust $ Sparse.set res.address account' res.ledger.tree }

  pure ledger''

touchedAccounts
  :: forall d
   . Ledger d Vesta.ScalarField
  -> SignedTransaction Vesta.ScalarField
  -> Array (Tuple (Address d) (Maybe (PublicKey Vesta.ScalarField)))
touchedAccounts { accountMap, nextAddress } transaction =
  let
    (SignedTransaction { transaction: Transaction { transfer: Transfer { to, from } } }) = transaction
    res =
      foldl
        ( \acc pk ->
            case Map.lookup pk accountMap of
              Nothing ->
                acc
                  { nextAddress = acc.nextAddress + one
                  , as = acc.as `Array.snoc` Tuple (Address acc.nextAddress) Nothing
                  }
              Just addr ->
                acc { as = acc.as `Array.snoc` Tuple addr (Just pk) }
        )
        { nextAddress, as: mempty }
        [ to, from ]
  in
    res.as