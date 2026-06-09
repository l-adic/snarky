-- | The ledger: a sparse Merkle tree of accounts plus the auxiliary
-- | address index a node keeps alongside it, together with pure utilities
-- | for working with it. There is deliberately no monad here — a ledger is
-- | just data, and these are plain functions over it. The advice monad
-- | that serves a circuit's requests against a ledger lives in
-- | `Snarky.Example.Transaction`.
-- |
-- | Most definitions are generic over the field `f`; only genesis is
-- | curve-bound (it mints Pallas keypairs whose coordinates are the public
-- | keys), so it is pinned to the example's `Vesta.ScalarField`.
module Snarky.Example.Ledger
  ( Ledger
  , lookupAddress
  , getAccount
  , balanceOf
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.MerkleTree.Sparse as Sparse
import Data.Newtype (un)
import JS.BigInt (BigInt)
import Snarky.Circuit.DSL (toField)
import Snarky.Circuit.RandomOracle (Digest)
import Snarky.Example.Types (Account, PublicKey, TokenAmount(..))

--------------------------------------------------------------------------------
-- The ledger

-- | A ledger: the account tree plus the public-key → address index a node
-- | maintains beside it (Mina assigns addresses sequentially, so we also
-- | track the next free slot). Signing keys are NOT ledger data and live
-- | with the wallet that produced them (see `genLedger`'s `keys`).
type Ledger d f =
  { tree :: Sparse.SparseMerkleTree d (Digest f) (Account f)
  , accountMap :: Map (PublicKey f) (Sparse.Address d) -- public key -> address
  , nextAddress :: BigInt -- next address to assign
  }

-- | Look up the address for a public key.
lookupAddress :: forall d f. Ord f => Ledger d f -> PublicKey f -> Maybe (Sparse.Address d)
lookupAddress ledger pk = Map.lookup pk ledger.accountMap

-- | Fetch the account stored at an address (if any).
getAccount :: forall d f. Ledger d f -> Sparse.Address d -> Maybe (Account f)
getAccount ledger addr = Sparse.get ledger.tree addr

--------------------------------------------------------------------------------
-- Token-amount utilities

-- | Read the underlying field value of a token amount.
balanceOf :: forall f. TokenAmount f -> f
balanceOf tb = toField (un TokenAmount tb)