-- | The snark-work protocol shared by the block producer and the worker: the
-- | unit of work and the proof it yields. Both ends depend only on this module,
-- | so the channel boundary between them is explicit.
-- |
-- | The `Merge` job is serializable for cross-process transport
-- | (`encodeMergeJob`/`decodeMergeJob`): each child proof goes through the
-- | pickles `CompiledProof` codec, the merged statement through its own codec.
-- | `Base` transport additionally needs the witness `Mask` codec (pending).
module Snarky.Example.Snark.Work
  ( WorkItem(..)
  , BaseJob
  , MergeJob
  , Proof
  , encodeMergeJob
  , decodeMergeJob
  ) where

import Prelude

import Data.Either (Either)
import Foreign (MultipleErrors)
import Pickles (CompiledProof)
import Pickles.Prove.SerializeProof (WidthDummies, decodeCompiledProof, encodeCompiledProof)
import Simple.JSON (readJSON, writeJSON)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Mask)
import Snarky.Example.Transaction (SignedTransaction, Statement, TxnStmt)

-- | A proof of the two-branch transaction-snark program (base or merge — same
-- | wrap VK, both `CompiledProof 2 TxnStmt`).
type Proof = CompiledProof 2 TxnStmt

-- | One base-proof job: the transaction, its witness, and its statement
-- | (`{ source = root Lᵢ, target = root Lᵢ₊₁ }`). What `processBlock` emits per
-- | transaction, and what a `Leaf` of the scan-state tree holds.
type BaseJob d =
  { tx :: SignedTransaction Vesta.ScalarField
  , mask :: Mask d
  , statement :: Statement Vesta.ScalarField
  }

-- | One merge job: the two child proofs and the merged statement they compose
-- | into (`{ source = proof1.source, target = proof2.target }`).
type MergeJob =
  { proof1 :: Proof
  , proof2 :: Proof
  , statement :: Statement Vesta.ScalarField
  }

-- | A unit of snark work: either prove a base transaction against its witness,
-- | or merge two child proofs.
data WorkItem d
  = Base (BaseJob d)
  | Merge MergeJob

-- | Serialize a merge job for transport: each child proof through the pickles
-- | `CompiledProof` codec (embedded as a nested string), the merged statement
-- | directly via its own codec.
encodeMergeJob :: MergeJob -> String
encodeMergeJob j = writeJSON
  { proof1: encodeCompiledProof j.proof1
  , proof2: encodeCompiledProof j.proof2
  , statement: j.statement
  }

-- | Parse a merge job. The child proofs are reconstructed with the program's
-- | `WidthDummies` (`Pickles.Prove.SerializeProof.mkWidthDummies`).
decodeMergeJob :: WidthDummies -> String -> Either MultipleErrors MergeJob
decodeMergeJob dummies s = do
  w <-
    readJSON s ::
      Either MultipleErrors
        { proof1 :: String, proof2 :: String, statement :: Statement Vesta.ScalarField }
  proof1 <- decodeCompiledProof dummies w.proof1
  proof2 <- decodeCompiledProof dummies w.proof2
  pure { proof1, proof2, statement: w.statement }
