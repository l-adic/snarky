-- | The snark-work protocol shared by the block producer and the worker: the
-- | unit of work and the proof it yields. Both ends depend only on this module,
-- | so the channel boundary between them is explicit.
-- |
-- | Both jobs are serializable for cross-process transport. A `Merge`
-- | (`encodeMergeJob`/`decodeMergeJob`) sends each child proof through the
-- | pickles `CompiledProof` codec and the merged statement through its own
-- | codec; a `Base` (`encodeBaseJob`/`decodeBaseJob`) serializes structurally —
-- | the witness `Mask` (a `SparseLedger`) already has `Read/WriteForeign`
-- | instances, so there are no proofs to embed.
module Snarky.Example.Snark.Work
  ( WorkItem(..)
  , BaseJob
  , MergeJob
  , Proof
  , encodeMergeJob
  , decodeMergeJob
  , encodeBaseJob
  , decodeBaseJob
  , encodeWorkItem
  , decodeWorkItem
  ) where

import Prelude

import Data.Either (Either(..))
import Foreign (ForeignError(..), MultipleErrors)
import Pickles (CompiledProof)
import Pickles.Prove.SerializeProof (decodeCompiledProof, encodeCompiledProof)
import Simple.JSON (readJSON, writeJSON)
import Snarky.Backend.Kimchi.Types (CRS)
import Snarky.Curves.Pasta (PallasG, VestaG)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Ledger (Mask)
import Snarky.Example.Transaction (SignedTransaction, Statement, TxnStmt)

-- | The SRSes a decode needs to rebuild proofs — any record carrying them, so
-- | the app `Env` can be passed directly.
type Srs r = { pallasSrs :: CRS PallasG, vestaSrs :: CRS VestaG | r }

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

-- | Parse a merge job. The child proofs are reconstructed from the SRSes (the
-- | decode builds the program's front-padding internally).
decodeMergeJob :: forall r. Srs r -> String -> Either MultipleErrors MergeJob
decodeMergeJob srs s = do
  w <-
    readJSON s
      :: Either MultipleErrors
           { proof1 :: String, proof2 :: String, statement :: Statement Vesta.ScalarField }
  proof1 <- decodeCompiledProof srs w.proof1
  proof2 <- decodeCompiledProof srs w.proof2
  pure { proof1, proof2, statement: w.statement }

-- | Serialize a base job: the transaction, witness mask, and statement all
-- | serialize structurally (no proofs to embed).
encodeBaseJob :: forall d. BaseJob d -> String
encodeBaseJob = writeJSON

-- | Parse a base job.
decodeBaseJob :: forall d. String -> Either MultipleErrors (BaseJob d)
decodeBaseJob = readJSON

-- | Serialize a work item (tagged base/merge) for transport.
encodeWorkItem :: forall d. WorkItem d -> String
encodeWorkItem = case _ of
  Base b -> writeJSON { tag: "base", base: b }
  Merge m -> writeJSON { tag: "merge", merge: encodeMergeJob m }

-- | Parse a work item. The merge branch reconstructs its child proofs from the
-- | SRSes; the base branch needs none.
decodeWorkItem :: forall d r. Srs r -> String -> Either MultipleErrors (WorkItem d)
decodeWorkItem srs s = do
  tagged <- readJSON s :: Either MultipleErrors { tag :: String }
  case tagged.tag of
    "base" -> do
      r <- readJSON s :: Either MultipleErrors { base :: BaseJob d }
      pure (Base r.base)
    "merge" -> do
      r <- readJSON s :: Either MultipleErrors { merge :: String }
      Merge <$> decodeMergeJob srs r.merge
    other -> Left (pure (ForeignError ("WorkItem: unknown tag " <> other)))
