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
-- |   ReaderT { currentTransaction :: Maybe (SignedTransaction (F f))
-- |           , ledger :: Ref (Ledger d f) } Effect
-- |
-- | A base prove supplies `currentTransaction = Just tx`; a merge prove
-- | (which witnesses no transaction) supplies `Nothing`. `TransferCompileM`
-- | is the compile-time twin whose advice instances throw (compilation
-- | discards `exists` bodies, so no request is ever served).
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
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sparse (Address)
import Data.MerkleTree.Sparse as Sparse
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Effect.Ref (Ref, read, write)
import Partial.Unsafe (unsafeCrashWith)
import Poseidon (class PoseidonField)
import Safe.Coerce (coerce)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, FVar)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Example.Ledger (Ledger, lookupAddress)
import Snarky.Example.Transaction.Types (SignedTransaction)
import Snarky.Example.Types (Account, PublicKey, TokenAmount)

--------------------------------------------------------------------------------
-- | Advice class for supplying the transaction being proven as a private
-- | witness. The pickled {source, target} statement does not carry the
-- | `SignedTransaction`; the prover conjures it in-circuit via `exists`,
-- | reading it from the witness monad's own instance.
class Monad m <= TransactionM m f | m -> f where
  getCurrentTransaction :: m (SignedTransaction f)

--------------------------------------------------------------------------------
-- Run-time advice monad

-- | Advice monad: a reader over the per-prove transaction plus a mutable
-- | ledger reference. The ledger is a `Ref` because `MerkleRequestM.setValue`
-- | mutates the tree in place as the circuit applies the transfer.
newtype TransferM d f a =
  TransferM
    ( ReaderT
        { currentTransaction :: Maybe (SignedTransaction f)
        , ledger :: Ref (Ledger d f)
        }
        Effect
        a
    )

derive newtype instance Functor (TransferM d f)
derive newtype instance Apply (TransferM d f)
derive newtype instance Applicative (TransferM d f)
derive newtype instance Bind (TransferM d f)
derive newtype instance Monad (TransferM d f)
derive newtype instance MonadRec (TransferM d f)
derive newtype instance MonadEffect (TransferM d f)
derive newtype instance MonadThrow Error (TransferM d f)

runTransferM
  :: forall d f
   . { currentTransaction :: Maybe (SignedTransaction f), ledger :: Ref (Ledger d f) }
  -> TransferM d f
       ~> Effect
runTransferM env (TransferM m) = runReaderT m env

getLedger :: forall d f. TransferM d f (Ledger d f)
getLedger = TransferM $ ask >>= \env -> liftEffect $ read env.ledger

modifyLedger :: forall d f. (Ledger d f -> Ledger d f) -> TransferM d f Unit
modifyLedger f = TransferM $ ask >>= \env -> liftEffect do
  ledger <- read env.ledger
  write (f ledger) env.ledger

-- | MerkleRequestM instance — serves Merkle paths from, and applies updates
-- | to, the ledger tree behind the reader's `ledger` reference.
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account f) (Account (FVar f))
  , CheckedType f (KimchiConstraint f) (TokenAmount (FVar f))
  , MerkleHashable (Account f) (Digest f)
  ) =>
  CMT.MerkleRequestM (TransferM d f) f (Account f) d where
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
instance Ord f => AccountMapM (TransferM d f) f d where
  getAccountId pk = do
    ledger <- getLedger
    case lookupAddress ledger pk of
      Just addr -> pure $ addr
      Nothing -> throwError $ error "getAccountId: public key not found in account map"

-- | TransactionM instance — serves the transaction this prove is proving,
-- | taken from the reader environment (the per-prove "arrow" input), NOT
-- | from ledger state.
instance TransactionM (TransferM d f) f where
  getCurrentTransaction = do
    env <- TransferM ask
    case env.currentTransaction of
      Just tx -> pure $ coerce tx
      Nothing -> throwError $ error "getCurrentTransaction: no current transaction set"

--------------------------------------------------------------------------------
-- Compile-time advice monad (throws on any request)

newtype TransferCompileM :: Int -> Type -> Type -> Type
newtype TransferCompileM d f a = TransferCompileM (Identity a)

derive newtype instance Functor (TransferCompileM d f)
derive newtype instance Apply (TransferCompileM d f)
derive newtype instance Applicative (TransferCompileM d f)
derive newtype instance Bind (TransferCompileM d f)
derive newtype instance Monad (TransferCompileM d f)
derive newtype instance MonadRec (TransferCompileM d f)

runTransferCompileM :: forall d f a. TransferCompileM d f a -> a
runTransferCompileM (TransferCompileM m) = un Identity m

instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account f) (Account (FVar f))
  , CheckedType f (KimchiConstraint f) (TokenAmount (FVar f))
  , MerkleHashable (Account f) (Digest f)
  ) =>
  CMT.MerkleRequestM (TransferCompileM d f) f (Account f) d where
  getElement _ = unsafeCrashWith "the impossible happened! unhandled request: getElement"
  getPath _ = unsafeCrashWith "the impossible happened! unhandled request: getPath"
  setValue _ _ = unsafeCrashWith "the impossible happened! unhandled request: setValue"

instance AccountMapM (TransferCompileM d f) f d where
  getAccountId _ = unsafeCrashWith "the impossible happened! unhandled request: getAccountId"

--------------------------------------------------------------------------------
-- | Advice monad for looking up account addresses from public keys.
-- |
-- | This typeclass allows circuits to "conjure" an address from a public key
-- | during witness generation. The prover provides the mapping externally.
class Monad m <= AccountMapM m f (d :: Int) | m -> f d where
  getAccountId :: PublicKey f -> m (Address d)
