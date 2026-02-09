module Snarky.Example.Circuits
  ( class AccountMapM
  , getAccountId
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
import Snarky.Circuit.DSL (class CircuitM, Bool(..), F(..), FVar, Snarky, assertEq, assertEqual_, const_, exists, read, sum_, unpack_)
import Snarky.Circuit.MerkleTree as CMT
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Constraint.Kimchi (KimchiConstraint)
import Snarky.Curves.Class (class FieldSizeInBits)
import Snarky.Example.Types (Account(..), PublicKey(..), TokenAmount(..), Transaction)

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

-- | Transfer tokens between accounts.
-- |
-- | This circuit:
-- | 1. Takes a transaction (public keys + amount)
-- | 2. Looks up addresses from public keys via AccountMapM
-- | 3. Fetches sender account, verifies ownership, debits the amount
-- | 4. Fetches receiver account, verifies ownership, credits the amount
-- | 5. Returns the new merkle root
-- |
-- | Note: Addresses are assigned sequentially in Mina (not derived from public keys).
-- | The circuit verifies the account at each address has the expected public key.
transfer
  :: forall t m f @d n _k
   . Reflectable d Int
  => PoseidonField f
  => FieldSizeInBits f n
  => Add 64 _k n
  => AccountMapM m f d
  => CMT.MerkleRequestM m f (Account (F f)) d (Account (FVar f))
  => MerkleHashable (Account (FVar f)) (Snarky (KimchiConstraint f) t m (Digest (FVar f)))
  => CircuitM f (KimchiConstraint f) t m
  => Digest (FVar f)
  -> Transaction (FVar f)
  -> Snarky (KimchiConstraint f) t m (Digest (FVar f))
transfer root { from, to, amount } = do
  -- Look up addresses from public keys (via advice/witness)
  -- The `exists` block witnesses the Address value as AddressVar circuit variables
  fromAddr <- exists do
    PublicKey (F fromPk) <- read from
    lift $ getAccountId (PublicKey (F fromPk))
  toAddr <- exists do
    PublicKey (F toPk) <- read to
    lift $ getAccountId (PublicKey (F toPk))

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