-- | The mask-backed advice monad: the per-transaction analog of
-- | `Snarky.Example.Transaction.Monad.TransferM`, but serving the circuit from
-- | a `Data.MerkleTree.Sparse.Mask` (a witness over only the slots the
-- | transaction touches) instead of the full `Ledger`.
-- |
-- | This is the prover-side witness provider for proving a single base
-- | transaction against its extracted witness (`Unchecked.touchedAccounts` +
-- | `Mask.fromSubset`). The circuit is unchanged — it speaks the same
-- | `MerkleRequestM` / `AccountMapM` / `TransactionM` interface; only the
-- | backing store differs:
-- |
-- |   * `MerkleRequestM`  → `Mask.get`/`getPath`/`set`
-- |   * `AccountMapM`     → `Mask.findIndex` against the mask's index map
-- |   * `TransactionM`    → the reader's per-prove transaction (same as TransferM)
module Snarky.Example.Transaction.MaskMonad
  ( TransferMaskM
  , runTransferMaskM
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse.Mask as Mask
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Effect.Ref (Ref, modify_, read)
import Safe.Coerce (coerce)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Mask)
import Snarky.Example.Transaction.Monad (class AccountMapM, class TransactionM)
import Snarky.Example.Transaction.Types (SignedTransaction)
import Snarky.Example.Types (Account)

-- | Advice monad: a reader over the per-prove transaction plus a mutable mask
-- | reference (the witness mutates in place as the circuit applies the transfer).
newtype TransferMaskM d a =
  TransferMaskM
    ( ReaderT
        { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField)
        , mask :: Ref (Mask d)
        }
        Effect
        a
    )

derive newtype instance Functor (TransferMaskM d)
derive newtype instance Apply (TransferMaskM d)
derive newtype instance Applicative (TransferMaskM d)
derive newtype instance Bind (TransferMaskM d)
derive newtype instance Monad (TransferMaskM d)
derive newtype instance MonadRec (TransferMaskM d)
derive newtype instance MonadEffect (TransferMaskM d)
derive newtype instance MonadThrow Error (TransferMaskM d)

runTransferMaskM
  :: forall d
   . { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField), mask :: Ref (Mask d) }
  -> TransferMaskM d
       ~> Effect
runTransferMaskM env (TransferMaskM m) = runReaderT m env

getMask :: forall d. TransferMaskM d (Mask d)
getMask = TransferMaskM $ ask >>= \env -> liftEffect $ read env.mask

modifyMask :: forall d. (Mask d -> Mask d) -> TransferMaskM d Unit
modifyMask g = TransferMaskM $ ask >>= \env -> liftEffect $ modify_ g env.mask

-- | MerkleRequestM — serves paths from, and applies updates to, the mask.
instance
  Reflectable d Int =>
  CMT.MerkleRequestM (TransferMaskM d) Vesta.ScalarField (Account Vesta.ScalarField) d where
  getElement addr = do
    mask <- getMask
    case Mask.get addr mask of
      Just v -> pure { value: v, path: Mask.getPath addr mask }
      Nothing -> throwError $ error "getElement: address not present in the witness"

  getPath addr = Mask.getPath addr <$> getMask

  setValue addr v = modifyMask (Mask.set addr v)

-- | AccountMapM — resolves a public key to its address via the mask's index.
instance AccountMapM (TransferMaskM d) d where
  getAccountId pk = do
    mask <- getMask
    case Mask.findIndex pk mask of
      Just addr -> pure addr
      Nothing -> throwError $ error "getAccountId: public key not present in the witness"

-- | TransactionM — serves the transaction being proven from the reader env.
instance TransactionM (TransferMaskM d) where
  getCurrentTransaction = do
    env <- TransferMaskM ask
    case env.currentTransaction of
      Just tx -> pure $ coerce tx
      Nothing -> throwError $ error "getCurrentTransaction: no current transaction set"
