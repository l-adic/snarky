-- | The merge DAG as every peer sees it: pure, derived entirely from the
-- | block's leaf statements (public). Each slot's content-address key is
-- | `stmtKey` of its statement; a merge slot is "ready" when both children's
-- | proofs are present in the (gossiped) have-set. No proofs are needed to
-- | compute any of this — only the leaf statements.
module Snarky.Example.P2P.Dag
  ( DagView
  , buildDag
  , keyOf
  , rootKey
  , ready
  ) where

import Prelude

import Data.Array as Array
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import Data.Set as Set
import Data.Tuple (Tuple(..))
import Snarky.Example.Merge (Stmt, slotStatementsOf, stmtKey)

type DagView =
  { n :: Int
  , keys :: Map Int String -- slot -> stmtKey
  }

-- | `leafStmts` ordered by slot ascending (leaf `j` at slot `n+j`).
buildDag :: Int -> Array Stmt -> DagView
buildDag n leafStmts =
  let
    internal = slotStatementsOf n leafStmts -- Map slot Stmt for slots 1..n-1
    leafKeys = Array.mapWithIndex (\j st -> Tuple (n + j) (stmtKey st)) leafStmts
    internalKeys = map (\(Tuple s st) -> Tuple s (stmtKey st)) (Map.toUnfoldable internal :: Array _)
    keys = Map.fromFoldable (leafKeys <> internalKeys)
  in
    { n, keys }

keyOf :: DagView -> Int -> String
keyOf dag slot = fromMaybe "" (Map.lookup slot dag.keys)

rootKey :: DagView -> String
rootKey dag = keyOf dag 1

-- | Internal slots whose two children are both present but which is not itself
-- | present yet — ascending (lowest slot first).
ready :: DagView -> Set String -> Array Int
ready dag have = Array.filter isReady (Array.range 1 (dag.n - 1))
  where
  isReady s =
    Set.member (keyOf dag (2 * s)) have
      && Set.member (keyOf dag (2 * s + 1)) have
      && not (Set.member (keyOf dag s) have)
