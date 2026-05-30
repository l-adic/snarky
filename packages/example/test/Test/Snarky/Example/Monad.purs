module Test.Snarky.Example.Monad
  ( TransferRefM
  , runTransferRefM
  , TransferState
  , TransferCompileM
  , runTransferCompileM
  , lookupAddress
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Control.Monad.Rec.Class (class MonadRec)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sparse as Sparse
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Effect.Ref (Ref, read, write)
import JS.BigInt (BigInt)
import Partial.Unsafe (unsafeCrashWith)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (class CheckedType, class CircuitType, F, FVar)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Pallas as Pallas
import Snarky.Example.Circuits (class AccountMapM, class TransactionM)
import Snarky.Example.Types (Account, PublicKey, SignedTransaction, TokenAmount)

--------------------------------------------------------------------------------
-- Test monad types

-- | State for the transfer test monad (using sparse merkle tree)
-- | Like Mina, we maintain a separate map from public key to address
type TransferState d f =
  { tree :: Sparse.SparseMerkleTree d (Digest (F f)) (Account (F f))
  , accountMap :: Map (PublicKey (F f)) (Sparse.Address d) -- public key -> address
  , privateKeys :: Map (PublicKey (F f)) Pallas.ScalarField -- public key -> signing key
  , nextAddress :: BigInt -- next address to assign
  -- | The transaction currently being proven (set before each base
  -- | prove). Served to the pickled base rule via `TransactionM`.
  , currentTransaction :: Maybe (SignedTransaction (F f))
  }

-- | Look up the address for a public key
lookupAddress :: forall d f. Ord f => TransferState d f -> PublicKey (F f) -> Maybe (Sparse.Address d)
lookupAddress state pk = Map.lookup pk state.accountMap

-- | Ref to the transfer state
type TransferStateRef d f = Ref (TransferState d f)

-- | Test monad that implements MerkleRequestM for sparse trees
newtype TransferRefM d f a = TransferRefM (ReaderT (TransferStateRef d f) Effect a)

derive newtype instance Functor (TransferRefM d f)
derive newtype instance Apply (TransferRefM d f)
derive newtype instance Applicative (TransferRefM d f)
derive newtype instance Bind (TransferRefM d f)
derive newtype instance Monad (TransferRefM d f)
derive newtype instance MonadRec (TransferRefM d f)
derive newtype instance MonadEffect (TransferRefM d f)
derive newtype instance MonadThrow Error (TransferRefM d f)

runTransferRefM :: forall d f. TransferStateRef d f -> TransferRefM d f ~> Effect
runTransferRefM ref (TransferRefM m) = runReaderT m ref

getStateRef :: forall d f. TransferRefM d f (TransferState d f)
getStateRef = TransferRefM $ ask >>= \ref -> liftEffect $ read ref

modifyStateRef
  :: forall d f
   . (TransferState d f -> TransferState d f)
  -> TransferRefM d f Unit
modifyStateRef f = TransferRefM $ ask >>= \ref -> liftEffect do
  state <- read ref
  write (f state) ref

-- | MerkleRequestM instance for TransferRefM (using sparse tree)
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account (F f)) (Account (FVar f))
  , CheckedType f (KimchiConstraint f) (TokenAmount (FVar f))
  , MerkleHashable (Account (F f)) (Digest (F f))
  ) =>
  CMT.MerkleRequestM (TransferRefM d f) f (Account (F f)) d (Account (FVar f)) where
  getElement (Sparse.Address addr) = do
    { tree } <- getStateRef
    let
      sparseAddr = Sparse.Address addr
      mval = Sparse.get tree sparseAddr
      path = Sparse.getWitness sparseAddr tree
    case mval of
      Just v -> pure { value: v, path }
      Nothing -> throwError $ error "getElement: address not set in sparse tree"

  getPath (Sparse.Address addr) = do
    { tree } <- getStateRef
    pure $ Sparse.getWitness (Sparse.Address addr) tree

  setValue (Sparse.Address addr) v = do
    { tree } <- getStateRef
    case Sparse.set (Sparse.Address addr) v tree of
      Just tree' -> modifyStateRef \state -> state { tree = tree' }
      Nothing -> throwError $ error "setValue: invalid address"

-- | AccountMapM instance for TransferRefM - looks up address from accountMap
instance Ord f => AccountMapM (TransferRefM d f) f d where
  getAccountId pk = do
    state <- getStateRef
    case lookupAddress state pk of
      Just addr -> pure addr
      Nothing -> throwError $ error "getAccountId: public key not found in account map"

-- | TransactionM instance — serves the `currentTransaction` set on the
-- | state before each base prove. This (with AccountMapM + MerkleRequestM
-- | above) is what lets the pickled base rule run at bare `TransferRefM`:
-- | all three are ordinary non-orphan instances on the app monad.
instance TransactionM (TransferRefM d f) f where
  getCurrentTransaction = do
    state <- getStateRef
    case state.currentTransaction of
      Just tx -> pure tx
      Nothing -> throwError $ error "getCurrentTransaction: no current transaction set"

--------------------------------------------------------------------------------
-- Compile-time monad (throws on any request)

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

-- | MerkleRequestM instance for compilation phase
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account (F f)) (Account (FVar f))
  , CheckedType f (KimchiConstraint f) (TokenAmount (FVar f))
  ) =>
  CMT.MerkleRequestM (TransferCompileM d f) f (Account (F f)) d (Account (FVar f)) where
  getElement _ = unsafeCrashWith "the impossible happened! unhandled request: getElement"
  getPath _ = unsafeCrashWith "the impossible happened! unhandled request: getPath"
  setValue _ _ = unsafeCrashWith "the impossible happened! unhandled request: setValue"

-- | AccountMapM instance for compilation phase - throws on any request
instance AccountMapM (TransferCompileM d f) f d where
  getAccountId _ = unsafeCrashWith "the impossible happened! unhandled request: getAccountId"