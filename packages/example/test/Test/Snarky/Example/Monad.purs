module Test.Snarky.Example.Monad
  ( TransferRefM
  , runTransferRefM
  , TransferState
  , TransferCompileM
  , runTransferCompileM
  ) where

import Prelude

import Control.Monad.Error.Class (class MonadThrow, throwError)
import Control.Monad.Reader (ReaderT, ask, runReaderT)
import Data.Identity (Identity(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sized (Address)
import Data.MerkleTree.Sized as SMT
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import Effect (Effect)
import Effect.Class (class MonadEffect, liftEffect)
import Effect.Exception (Error, error)
import Effect.Ref (Ref, read, write)
import Partial.Unsafe (unsafeCrashWith)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (F, FVar)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Circuit.Types (class CheckedType, class CircuitType)
import Snarky.Example.Circuits (class AccountMapM)
import Snarky.Example.Types (Account, PublicKey)

--------------------------------------------------------------------------------
-- Test monad types

-- | State for the transfer test monad
type TransferState d f =
  { tree :: SMT.MerkleTree d (Digest (F f)) (Account (F f))
  , accountMap :: Map (PublicKey (F f)) (Address d)
  }

-- | Ref to the transfer state
type TransferStateRef d f = Ref (TransferState d f)

-- | Test monad that implements both MerkleRequestM and AccountMapM
newtype TransferRefM d f a = TransferRefM (ReaderT (TransferStateRef d f) Effect a)

derive newtype instance Functor (TransferRefM d f)
derive newtype instance Apply (TransferRefM d f)
derive newtype instance Applicative (TransferRefM d f)
derive newtype instance Bind (TransferRefM d f)
derive newtype instance Monad (TransferRefM d f)
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

-- | MerkleRequestM instance for TransferRefM
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account (F f)) (Account (FVar f))
  , CheckedType (Account (FVar f)) c
  , MerkleHashable (Account (F f)) (Digest (F f))
  ) =>
  CMT.MerkleRequestM (TransferRefM d f) f (Account (F f)) c d (Account (FVar f)) where
  getElement (SMT.Address addr) = do
    { tree } <- getStateRef
    let
      mval = SMT.get tree (SMT.Address addr)
      mpath = SMT.getPath tree (SMT.Address addr)
    case mval, mpath of
      Just v, Just p -> pure { value: v, path: p }
      _, _ -> throwError $ error "getElement: invalid address"

  getPath (SMT.Address addr) = do
    { tree } <- getStateRef
    case SMT.getPath tree (SMT.Address addr) of
      Just p -> pure p
      Nothing -> throwError $ error "getPath: invalid address"

  setValue (SMT.Address addr) v = do
    { tree } <- getStateRef
    case SMT.set tree (SMT.Address addr) v of
      Just tree' -> modifyStateRef \state -> state { tree = tree' }
      Nothing -> throwError $ error "setValue: invalid address"

-- | AccountMapM instance for TransferRefM
instance
  ( Reflectable d Int
  , PoseidonField f
  ) =>
  AccountMapM (TransferRefM d f) f d where
  getAccountId pubKey = do
    { accountMap } <- getStateRef
    case Map.lookup pubKey accountMap of
      Just addr -> pure addr
      Nothing -> throwError $ error $ "getAccountId: unknown public key"

--------------------------------------------------------------------------------
-- Compile-time monad (throws on any request)

newtype TransferCompileM :: Int -> Type -> Type -> Type
newtype TransferCompileM d f a = TransferCompileM (Identity a)

derive newtype instance Functor (TransferCompileM d f)
derive newtype instance Apply (TransferCompileM d f)
derive newtype instance Applicative (TransferCompileM d f)
derive newtype instance Bind (TransferCompileM d f)
derive newtype instance Monad (TransferCompileM d f)

runTransferCompileM :: forall d f a. TransferCompileM d f a -> a
runTransferCompileM (TransferCompileM m) = un Identity m

-- | MerkleRequestM instance for compilation phase
instance
  ( Reflectable d Int
  , PoseidonField f
  , CircuitType f (Account (F f)) (Account (FVar f))
  , CheckedType (Account (FVar f)) c
  ) =>
  CMT.MerkleRequestM (TransferCompileM d f) f (Account (F f)) c d (Account (FVar f)) where
  getElement _ = unsafeCrashWith "the impossible happened! unhandled request: getElement"
  getPath _ = unsafeCrashWith "the impossible happened! unhandled request: getPath"
  setValue _ _ = unsafeCrashWith "the impossible happened! unhandled request: setValue"

-- | AccountMapM instance for compilation phase
instance
  ( Reflectable d Int
  , PoseidonField f
  ) =>
  AccountMapM (TransferCompileM d f) f d where
  getAccountId _ = unsafeCrashWith "the impossible happened! unhandled request: getAccountId"