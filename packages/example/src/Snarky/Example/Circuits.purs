module Snarky.Example.Circuits
  ( class AccountMapM
  , getAccountId
  , getAccount
  , transfer
  ) where

import Prelude

import Control.Monad.Trans.Class (lift)
import Data.Array as Array
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sized (Address)
import Data.Reflectable (class Reflectable)
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertEqual_, exists, read, unpack_)
import Snarky.Circuit.DSL.Assert (assertEq)
import Snarky.Circuit.DSL.Field (sum_)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Circuit.Types (Bool(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Example.Types (Account(..), PublicKey, TokenAmount(..), Transaction(..))

--------------------------------------------------------------------------------
-- | Advice monad for looking up account addresses from public keys.
-- |
-- | This typeclass allows circuits to "conjure" an address from a public key
-- | during witness generation. The prover provides the mapping externally.
class Monad m <= AccountMapM m f (d :: Int) | m -> f d where
  getAccountId :: PublicKey (F f) -> m (Address d)

--------------------------------------------------------------------------------

-- | Assert that a field element is a valid unsigned 64-bit integer (0 to 2^64 - 1).
-- | This unpacks the field element to its bit representation and checks that
-- | all bits above position 63 are zero.
assertU64
  :: forall f c t m n rest
   . CircuitM f c t m
  => FieldSizeInBits f n
  => Add 64 rest n
  => TokenAmount (FVar f)
  -> Snarky c t m Unit
assertU64 (TokenAmount v) = do
  -- Unpack to n bits (255 for pasta curves)
  allBits <- unpack_ v
  -- Drop the lower 64 bits, keeping the higher (n - 64) bits
  let higherBits = Vector.drop @64 allBits
  -- Check that the sum of higher bits is zero (i.e., all are false)
  -- Convert Vector to Array and coerce BoolVar to FVar for sum_
  let higherBitsArray = Array.fromFoldable higherBits
  assertEqual_ (sum_ (coerce higherBitsArray)) (const_ zero)

-- | Get an account from the merkle tree and verify ownership.
-- |
-- | This circuit:
-- | 1. Takes the current root and expected public key as inputs
-- | 2. Conjures the address from the public key via AccountMapM
-- | 3. Retrieves the account at that address
-- | 4. Asserts the account's public key matches the expected public key
-- | 5. Returns the account
getAccount
  :: forall t m f d
   . Reflectable d Int
  => PoseidonField f
  => AccountMapM m f d
  => CMT.MerkleRequestM m f (Account (F f)) (KimchiConstraint f) d (Account (FVar f))
  => MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => Digest (FVar f)
  -> PublicKey (FVar f)
  -> Snarky (KimchiConstraint f) t m (Account (FVar f))
getAccount root expectedPubKey = do
  -- Conjure the address from the public key
  addr <- exists do
    pk <- read expectedPubKey
    lift $ getAccountId pk
  -- Get the account from the merkle tree
  account@(Account { publicKey }) <- CMT.get addr root
  -- Assert the public key matches
  assertEq publicKey expectedPubKey
  pure account

-- | Transfer tokens between accounts.
-- |
-- | This circuit:
-- | 1. Conjures addresses for both sender and receiver via AccountMapM
-- | 2. Fetches sender account, verifies ownership, debits the amount
-- | 3. Fetches receiver account, verifies ownership, credits the amount
-- | 4. Returns the new merkle root
-- |
-- | Note: Does not check for overflow/underflow.
transfer
  :: forall t m f d n _k
   . Reflectable d Int
  => PoseidonField f
  => FieldSizeInBits f n
  => Add 64 _k n
  => AccountMapM m f d
  => CMT.MerkleRequestM m f (Account (F f)) (KimchiConstraint f) d (Account (FVar f))
  => MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => Digest (FVar f)
  -> Transaction (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
transfer root (Transaction { from, to, amount }) = do
  -- Conjure addresses for sender and receiver
  fromAddr <- exists do
    pk <- read from
    lift $ getAccountId pk
  toAddr <- exists do
    pk <- read to
    lift $ getAccountId pk
  -- Debit sender: verify ownership and subtract amount
  { root: root' } <- CMT.fetchAndUpdate fromAddr root \(Account acc) -> do
    -- Verify sender owns this account
    assertEq acc.publicKey from
    -- Debit the amount
    newBalance <- pure acc.tokenBalance - pure amount
    assertU64 newBalance
    pure $ Account acc { tokenBalance = newBalance }
  -- Credit receiver: verify ownership and add amount
  { root: root'' } <- CMT.fetchAndUpdate toAddr root' \(Account acc) -> do
    -- Verify receiver owns this account
    assertEq acc.publicKey to
    -- Credit the amount
    newBalance <- pure acc.tokenBalance + pure amount
    assertU64 newBalance
    pure $ Account acc { tokenBalance = newBalance }
  pure root''