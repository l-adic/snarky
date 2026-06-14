-- | Shared merge-tree primitives used by both the browser merge client
-- | (`Snarky.Example.WebMerge`, with stepping/caching) and the server merger
-- | (`Snarky.Example.MergeServer`, plain). Reconstruct base proofs, derive
-- | each heap slot's structural statement, and reduce the perfect binary tree
-- | bottom-up by merging children into parents.
module Snarky.Example.Merge
  ( Depth
  , Stmt
  , Node
  , mkWidthDummies
  , decodeNode
  , requireNode
  , slotStatements
  , slotStatementsOf
  , stmtKey
  , encodeStmt
  , decodeStmt
  , mergeTree
  ) where

import Prelude

import Data.Array as Array
import Data.Either (Either(..))
import Data.Map (Map)
import Data.Map as Map
import Data.Maybe (Maybe(..))
import Data.Newtype (unwrap)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Exception (throw)
import Foreign (MultipleErrors)
import Partial.Unsafe (unsafePartial)
import Pickles (CompiledProof)
import Pickles.Dummy (dummyIpaChallenges)
import Pickles.Prove.SerializeProof (WidthDummies, reconstructCompiledProof)
import Pickles.Step.Dummy (baseCaseDummies, computeDummySgValues)
import Pickles.Types (StatementIO(..))
import Simple.JSON (readJSON, writeJSON)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Circuit.RandomOracle (Digest(..))
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Env (Env)
import Snarky.Example.Snark.LeafCodec (decodeLeaf)
import Snarky.Example.Transaction.Checked (Statement(..), TxnStmt)

type Depth = 4

type Stmt =
  { source :: Digest Vesta.ScalarField
  , target :: Digest Vesta.ScalarField
  }

type Node =
  { source :: Digest Vesta.ScalarField
  , target :: Digest Vesta.ScalarField
  , proof :: CompiledProof 2 TxnStmt
  }

mkWidthDummies :: CRS PallasG -> CRS VestaG -> WidthDummies
mkWidthDummies pallasSrs vestaSrs =
  let
    dummySgsMax = computeDummySgValues (baseCaseDummies { maxProofsVerified: 0 }) pallasSrs vestaSrs
  in
    { dummyOldBp: dummyIpaChallenges.stepExpanded
    , dummyMsgWrap: dummyIpaChallenges.wrapExpanded
    , dummyChalPolyComm: dummySgsMax.ipa.wrap.sg
    }

decodeNode :: WidthDummies -> String -> Effect Node
decodeNode dummies s = case decodeLeaf s of
  Left err -> throw (show err)
  Right scp ->
    let
      StatementIO { input: Statement { source, target } } = scp.statement
    in
      pure { source, target, proof: reconstructCompiledProof dummies scp }

requireNode :: Int -> Map Int Node -> Effect Node
requireNode slot mp = case Map.lookup slot mp of
  Just node -> pure node
  Nothing -> throw ("Merge: missing proof at slot " <> show slot)

-- | Each internal slot's structural statement: `source` of its leftmost leaf,
-- | `target` of its rightmost (the descent always lands on a valid leaf).
slotStatements :: Int -> Array Node -> Map Int Stmt
slotStatements n leaves =
  slotStatementsOf n (map (\nd -> { source: nd.source, target: nd.target }) leaves)

-- | Like `slotStatements` but over bare leaf statements (no proofs needed) —
-- | a merge peer derives the whole slot→statement map from the leaf statements
-- | it receives over the wire, without ever reconstructing a proof.
slotStatementsOf :: Int -> Array Stmt -> Map Int Stmt
slotStatementsOf n leaves =
  Map.fromFoldable (map (\s -> Tuple s (slotStmt s)) (Array.range 1 (n - 1)))
  where
  descend f i = if i >= n then i else descend f (f i)
  leafAt i = unsafePartial (Array.unsafeIndex leaves (i - n))
  slotStmt s =
    { source: (leafAt (descend (\i -> 2 * i) s)).source
    , target: (leafAt (descend (\i -> 2 * i + 1) s)).target
    }

-- | A node's IndexedDB / content-address cache key (its two ledger digests).
-- | Equal to `encodeStmt`; kept as a separate name for call-site clarity.
stmtKey :: Stmt -> String
stmtKey = encodeStmt

-- | Serialize a statement (its two ledger-root digests) to a JSON string —
-- | the wire form for leaf statements and the content-address key.
encodeStmt :: Stmt -> String
encodeStmt st = writeJSON { source: unwrap st.source, target: unwrap st.target }

decodeStmt :: String -> Either MultipleErrors Stmt
decodeStmt s = do
  w :: { source :: Vesta.ScalarField, target :: Vesta.ScalarField } <- readJSON s
  pure { source: Digest w.source, target: Digest w.target }

-- | Plain bottom-up reduction (no stepping/caching): merge slots n-1 .. 1.
mergeTree :: Env Depth -> Int -> Map Int Stmt -> Map Int Node -> Effect Node
mergeTree env n stmts mp0 = go (n - 1) mp0
  where
  go s mp
    | s < 1 = requireNode 1 mp
    | otherwise = do
        stmt <- case Map.lookup s stmts of
          Just st -> pure st
          Nothing -> throw ("Merge: no statement for slot " <> show s)
        a <- requireNode (2 * s) mp
        b <- requireNode (2 * s + 1) mp
        let statement = Statement { source: stmt.source, target: stmt.target }
        proof <- env.compiledTx.mergeProver { proof1: a.proof, proof2: b.proof, statement }
        go (s - 1) (Map.insert s { source: stmt.source, target: stmt.target, proof } mp)
