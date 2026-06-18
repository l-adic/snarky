-- | A shallow, human-readable summary of a snark work item, peeked from its
-- | encoded JSON WITHOUT the SRS — so it covers only the public parts: every
-- | job's statement (the ledger transition it proves) and, for a base job, the
-- | transaction (transfer amount + recipient). A merge's child proofs stay opaque
-- | (decoding them needs the SRS), so `jobSummary` is a deliberately lossy
-- | projection, NOT a full `WorkItem` decode. Pure (no browser, no SRS), so it is
-- | unit-testable in Node; the P2P worker peer uses `describeJob` for its UI label.
module Snarky.Example.Snark.JobSummary
  ( StmtPeek
  , JobSummary(..)
  , jobSummary
  , describeJob
  , fieldToDec
  , transition
  , shortHex
  ) where

import Prelude

import Data.Either (Either(..))
import Data.String as String
import Fmt (fmt)
import JS.BigInt as BigInt
import Simple.JSON (readJSON)
import Snarky.Curves.Class (fromHexLe, toBigInt)
import Snarky.Curves.Vesta as Vesta

-- | The public statement both job kinds prove: the ledger Merkle-root transition
-- | (`source → target`). Serialized as two little-endian field hex strings.
type StmtPeek = { source :: String, target :: String }

-- | Render a work-item field (a little-endian hex, how the WorkItem's
-- | `Vesta.ScalarField` values serialize) as a decimal string.
fieldToDec :: String -> String
fieldToDec hex = BigInt.toString (toBigInt (fromHexLe hex :: Vesta.ScalarField))

-- | A short fingerprint of a 32-byte field hex (for display only).
shortHex :: String -> String
shortHex h = String.take 8 h <> "…"

-- | `source → target`, both shortened.
transition :: StmtPeek -> String
transition s = shortHex s.source <> " → " <> shortHex s.target

data JobSummary
  = BaseJob { transition :: StmtPeek, amount :: String, to :: String }
  | MergeJob StmtPeek
  -- The raw tag, for a job we recognized but couldn't peek further into.
  | OtherJob String

-- | Decode a job's public summary from its encoded JSON (lossy by design).
jobSummary :: String -> JobSummary
jobSummary work = case readJSON work :: Either _ { tag :: String } of
  Right { tag: "base" } ->
    case
      readJSON work
        :: Either _
             { base ::
                 { statement :: StmtPeek
                 , tx :: { transaction :: { transfer :: { to :: { x :: String }, amount :: String } } }
                 }
             }
      of
      Right { base: b } ->
        BaseJob { transition: b.statement, amount: b.tx.transaction.transfer.amount, to: b.tx.transaction.transfer.to.x }
      Left _ -> OtherJob "base"
  Right { tag: "merge" } ->
    case readJSON work :: Either _ { merge :: String } of
      Right { merge } -> case readJSON merge :: Either _ { statement :: StmtPeek } of
        Right { statement } -> MergeJob statement
        Left _ -> OtherJob "merge"
      Left _ -> OtherJob "merge"
  _ -> OtherJob "job"

-- | A one-line human label for a job (UI / logs).
describeJob :: String -> String
describeJob work = case jobSummary work of
  BaseJob b -> fmt @"base · transfer {amount} → {to} · ledger {transition}"
    { amount: fieldToDec b.amount, to: shortHex b.to, transition: transition b.transition }
  MergeJob s -> fmt @"merge · ledger {transition}" { transition: transition s }
  OtherJob tag -> tag
