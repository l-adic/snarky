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
  , empty
  , Mask
  , emptyMask
  ) where

import Prelude

import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe)
import Data.MerkleTree (defaultHash)
import Data.MerkleTree.Sparse as Sparse
import Data.MerkleTree.Sparse.Mask (SparseLedger, ofHash)
import Data.Newtype (un)
import Data.Reflectable (class Reflectable)
import JS.BigInt (BigInt)
import Poseidon (class PoseidonField)
import Snarky.Circuit.DSL (toField)
import Snarky.Circuit.RandomOracle (class Hashable, Digest)
import Snarky.Curves.Vesta as Vesta
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

empty
  :: forall @d @f
   . PoseidonField f
  => Hashable (Account f) f
  => Reflectable d Int
  => Ledger d f
empty =
  { tree: Sparse.empty
  , accountMap: Map.empty
  , nextAddress: zero
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

type Mask d f = SparseLedger d (Digest f) (PublicKey f) (Account f)

-- | An empty witness: a fully-collapsed mask. Used as the (never-read) mask env
-- | for merge work (merge touches no ledger advice) and to compile.
emptyMask :: forall d. Mask d Vesta.ScalarField
emptyMask = ofHash (defaultHash @(Account Vesta.ScalarField) :: Digest Vesta.ScalarField)