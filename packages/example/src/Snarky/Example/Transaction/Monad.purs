-- | The prover-side advice monad and its compile-time twin, plus the
-- | `TransactionM` advice class they (and the circuit rules) speak through.
-- |
-- | `TransferM` answers a circuit's advice requests (`MerkleRequestM` /
-- | `AccountMapM` / `TransactionM`) against a live ledger and the particular
-- | transaction being proven. The transaction is NOT ledger state — it is the
-- | "arrow" mapping one ledger to the next — so it rides the monad's reader
-- | environment as an explicit per-prove input alongside the (mutable) ledger
-- | reference:
-- |
-- |   ReaderT { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField)
-- |           , ledger :: Ref (Ledger d) } Effect
-- |
-- | A base prove supplies `currentTransaction = Just tx`; a merge prove
-- | (which witnesses no transaction) supplies `Nothing`. `TransferCompileM`
-- | is the compile-time twin whose advice instances throw (compilation
-- | discards `exists` bodies, so no request is ever served).
-- |
-- | Everything here is value-only, so the field is pinned to the example's
-- | `Vesta.ScalarField` rather than carried as a parameter.
module Snarky.Example.Transaction.Monad
  ( class TransactionM
  , getCurrentTransaction
  , TransferM
  , runTransferM
  , TransferCompileM
  , runTransferCompileM
  , class AccountMapM
  , getAccountId
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Identity (Identity(..))
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Sparse (Address)
import Data.MerkleTree.Sparse as Sparse
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Effect.Ref (Ref, read, write)
import Partial.Unsafe (unsafeCrashWith)
import Safe.Coerce (coerce)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Ledger, lookupAddress)
import Snarky.Example.Transaction.Types (SignedTransaction)
import Snarky.Example.Types (Account, PublicKey)

--------------------------------------------------------------------------------
-- | Advice class for supplying the transaction being proven as a private
-- | witness. The pickled {source, target} statement does not carry the
-- | `SignedTransaction`; the prover conjures it in-circuit via `exists`,
-- | reading it from the witness monad's own instance.
class Monad m <= TransactionM m where
  getCurrentTransaction :: m (SignedTransaction Vesta.ScalarField)

--------------------------------------------------------------------------------
-- Run-time advice monad

-- | Advice monad: a reader over the per-prove transaction plus a mutable
-- | ledger reference. The ledger is a `Ref` because `MerkleRequestM.setValue`
-- | mutates the tree in place as the circuit applies the transfer.
newtype TransferM d a =
  TransferM
    ( ReaderT
        { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField)
        , ledger :: Ref (Ledger d)
        }
        Effect
        a
    )

derive newtype instance Functor (TransferM d)
derive newtype instance Apply (TransferM d)
derive newtype instance Applicative (TransferM d)
derive newtype instance Bind (TransferM d)
derive newtype instance Monad (TransferM d)
derive newtype instance MonadRec (TransferM d)
derive newtype instance MonadEffect (TransferM d)
derive newtype instance MonadThrow Error (TransferM d)

runTransferM
  :: forall d
   . { currentTransaction :: Maybe (SignedTransaction Vesta.ScalarField), ledger :: Ref (Ledger d) }
  -> TransferM d
       ~> Effect
runTransferM env (TransferM m) = runReaderT m env

getLedger :: forall d. TransferM d (Ledger d)
getLedger = TransferM $ ask >>= \env -> liftEffect $ read env.ledger

modifyLedger :: forall d. (Ledger d -> Ledger d) -> TransferM d Unit
modifyLedger f = TransferM $ ask >>= \env -> liftEffect do
  ledger <- read env.ledger
  write (f ledger) env.ledger

-- | MerkleRequestM instance — serves Merkle paths from, and applies updates
-- | to, the ledger tree behind the reader's `ledger` reference.
instance
  Reflectable d Int =>
  CMT.MerkleRequestM (TransferM d) Vesta.ScalarField (Account Vesta.ScalarField) d where
  getElement addr = do
    { tree } <- getLedger
    case Sparse.get tree addr of
      Just v -> pure { value: v, path: Sparse.getWitness addr tree }
      Nothing -> throwError $ error "getElement: address not set in sparse tree"

  getPath addr = do
    { tree } <- getLedger
    pure $ Sparse.getWitness addr tree

  setValue addr v = do
    { tree } <- getLedger
    case Sparse.set addr v tree of
      Just tree' -> modifyLedger _ { tree = tree' }
      Nothing -> throwError $ error "setValue: invalid address"

-- | AccountMapM instance — resolves a public key to its ledger address.
instance AccountMapM (TransferM d) d where
  getAccountId pk = do
    ledger <- getLedger
    case lookupAddress ledger pk of
      Just addr -> pure $ addr
      Nothing -> throwError $ error "getAccountId: public key not found in account map"

-- | TransactionM instance — serves the transaction this prove is proving,
-- | taken from the reader environment (the per-prove "arrow" input), NOT
-- | from ledger state.
instance TransactionM (TransferM d) where
  getCurrentTransaction = do
    env <- TransferM ask
    case env.currentTransaction of
      Just tx -> pure $ coerce tx
      Nothing -> throwError $ error "getCurrentTransaction: no current transaction set"

--------------------------------------------------------------------------------
-- Compile-time advice monad (throws on any request)

newtype TransferCompileM :: Int -> Type -> Type
newtype TransferCompileM d a = TransferCompileM (Identity a)

derive newtype instance Functor (TransferCompileM d)
derive newtype instance Apply (TransferCompileM d)
derive newtype instance Applicative (TransferCompileM d)
derive newtype instance Bind (TransferCompileM d)
derive newtype instance Monad (TransferCompileM d)
derive newtype instance MonadRec (TransferCompileM d)

runTransferCompileM :: forall d a. TransferCompileM d a -> a
runTransferCompileM (TransferCompileM m) = un Identity m

instance
  CMT.MerkleRequestM (TransferCompileM d) Vesta.ScalarField (Account Vesta.ScalarField) d where
  getElement _ = unsafeCrashWith "the impossible happened! unhandled request: getElement"
  getPath _ = unsafeCrashWith "the impossible happened! unhandled request: getPath"
  setValue _ _ = unsafeCrashWith "the impossible happened! unhandled request: setValue"

instance AccountMapM (TransferCompileM d) d where
  getAccountId _ = unsafeCrashWith "the impossible happened! unhandled request: getAccountId"

--------------------------------------------------------------------------------
-- | Advice monad for looking up account addresses from public keys.
-- |
-- | This typeclass allows circuits to "conjure" an address from a public key
-- | during witness generation. The prover provides the mapping externally.
class Monad m <= AccountMapM m (d :: Int) | m -> d where
  getAccountId :: PublicKey Vesta.ScalarField -> m (Address d)
