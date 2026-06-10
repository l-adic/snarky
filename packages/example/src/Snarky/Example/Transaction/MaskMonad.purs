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
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sparse.Mask as Mask
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Effect.Ref (Ref, modify_, read)
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, FVar)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Example.Ledger (Mask)
import Snarky.Example.Transaction.Monad (class AccountMapM, class TransactionM)
import Snarky.Example.Transaction.Types (SignedTransaction)
import Snarky.Example.Types (Account, TokenAmount)

-- | Advice monad: a reader over the per-prove transaction plus a mutable mask
-- | reference (the witness mutates in place as the circuit applies the transfer).
newtype TransferMaskM d f a =
  TransferMaskM
    ( ReaderT
        { currentTransaction :: Maybe (SignedTransaction f)
        , mask :: Ref (Mask d f)
        }
        Effect
        a
    )

derive newtype instance Functor (TransferMaskM d f)
derive newtype instance Apply (TransferMaskM d f)
derive newtype instance Applicative (TransferMaskM d f)
derive newtype instance Bind (TransferMaskM d f)
derive newtype instance Monad (TransferMaskM d f)
derive newtype instance MonadRec (TransferMaskM d f)
derive newtype instance MonadEffect (TransferMaskM d f)
derive newtype instance MonadThrow Error (TransferMaskM d f)

runTransferMaskM
  :: forall d f
   . { currentTransaction :: Maybe (SignedTransaction f), mask :: Ref (Mask d f) }
  -> TransferMaskM d f
       ~> Effect
runTransferMaskM env (TransferMaskM m) = runReaderT m env

getMask :: forall d f. TransferMaskM d f (Mask d f)
getMask = TransferMaskM $ ask >>= \env -> liftEffect $ read env.mask

modifyMask :: forall d f. (Mask d f -> Mask d f) -> TransferMaskM d f Unit
modifyMask g = TransferMaskM $ ask >>= \env -> liftEffect $ modify_ g env.mask

-- | MerkleRequestM — serves paths from, and applies updates to, the mask.
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account f) (Account (FVar f))
  , CheckedType f (KimchiConstraint f) (TokenAmount (FVar f))
  , MerkleHashable (Account f) (Digest f)
  ) =>
  CMT.MerkleRequestM (TransferMaskM d f) f (Account f) d where
  getElement addr = do
    mask <- getMask
    case Mask.get addr mask of
      Just v -> pure { value: v, path: Mask.getPath addr mask }
      Nothing -> throwError $ error "getElement: address not present in the witness"

  getPath addr = Mask.getPath addr <$> getMask

  setValue addr v = modifyMask (Mask.set addr v)

-- | AccountMapM — resolves a public key to its address via the mask's index.
instance Ord f => AccountMapM (TransferMaskM d f) f d where
  getAccountId pk = do
    mask <- getMask
    case Mask.findIndex pk mask of
      Just addr -> pure addr
      Nothing -> throwError $ error "getAccountId: public key not present in the witness"

-- | TransactionM — serves the transaction being proven from the reader env.
instance TransactionM (TransferMaskM d f) f where
  getCurrentTransaction = do
    env <- TransferMaskM ask
    case env.currentTransaction of
      Just tx -> pure $ coerce tx
      Nothing -> throwError $ error "getCurrentTransaction: no current transaction set"