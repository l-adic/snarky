module Snarky.Example.Circuits
  ( addressFromPublicKey
  , getAccount
  , transfer
  ) where

import Prelude

import Data.Array as Array
import Data.MerkleTree.Hashable (class MerkleHashable)
import Data.MerkleTree.Sized (AddressVar(..))
import Data.Reflectable (class Reflectable)
import Data.Vector as Vector
import Poseidon (class PoseidonField)
import Prim.Int (class Add)
import Safe.Coerce (coerce)
import Snarky.Circuit.CVar (const_)
import Snarky.Circuit.DSL (class CircuitM, F, FVar, Snarky, assertEqual_, unpack_)
import Snarky.Circuit.DSL.Assert (assertEq)
import Snarky.Circuit.DSL.Field (sum_)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest(..), hashVec)
import Snarky.Circuit.Types (Bool(..))
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Example.Types (Account(..), PublicKey(..), TokenAmount(..), Transaction(..))

--------------------------------------------------------------------------------
-- | Compute the address for a public key by hashing it
-- |
-- | The address is derived deterministically: address = hash(publicKey) mod 2^depth
-- | This is computed in-circuit using Poseidon hash.
addressFromPublicKey
  :: forall d f t m n rest
   . Reflectable d Int
  => PoseidonField f
  => FieldSizeInBits f n
  => Add d rest n
  => CircuitM f (KimchiConstraint f) t m
  => PublicKey (FVar f)
  -> Snarky (KimchiConstraint f) t m (AddressVar d f)
addressFromPublicKey (PublicKey pk) = do
  -- Hash the public key to get a field element
  Digest h <- hashVec [ pk ]
  -- Unpack to bits and take the first d bits as the address
  allBits <- unpack_ h
  pure $ AddressVar $ Vector.take @d allBits

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
-- | 2. Computes the address by hashing the public key
-- | 3. Retrieves the account at that address
-- | 4. Asserts the account's public key matches the expected public key
-- | 5. Returns the account
getAccount
  :: forall t m f d n rest
   . Reflectable d Int
  => PoseidonField f
  => FieldSizeInBits f n
  => Add d rest n
  => CMT.MerkleRequestM m f (Account (F f)) (KimchiConstraint f) d (Account (FVar f))
  => MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => Digest (FVar f)
  -> PublicKey (FVar f)
  -> Snarky (KimchiConstraint f) t m (Account (FVar f))
getAccount root expectedPubKey = do
  -- Compute the address from the public key
  addr :: AddressVar d f <- addressFromPublicKey expectedPubKey
  -- Get the account from the merkle tree
  account@(Account { publicKey }) <- CMT.get addr root
  -- Assert the public key matches
  assertEq publicKey expectedPubKey
  pure account

-- | Transfer tokens between accounts.
-- |
-- | This circuit:
-- | 1. Computes addresses for both sender and receiver by hashing their public keys
-- | 2. Fetches sender account, verifies ownership, debits the amount
-- | 3. Fetches receiver account, verifies ownership, credits the amount
-- | 4. Returns the new merkle root
-- |
-- | Note: Does not check for overflow/underflow.
-- | TODO: Handle transfer to new accounts (empty slots)
transfer
  :: forall t m f @d n _k _r
   . Reflectable d Int
  => PoseidonField f
  => FieldSizeInBits f n
  => Add 64 _k n
  => Add d _r n
  => CMT.MerkleRequestM m f (Account (F f)) (KimchiConstraint f) d (Account (FVar f))
  => MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => Digest (FVar f)
  -> Transaction (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
transfer root (Transaction { from, to, amount }) = do
  -- Compute addresses from public keys
  fromAddr :: AddressVar d f <- addressFromPublicKey from
  toAddr :: AddressVar d f <- addressFromPublicKey to
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