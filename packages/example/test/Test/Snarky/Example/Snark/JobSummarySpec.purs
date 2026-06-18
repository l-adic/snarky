-- | Unit tests for `Snarky.Example.Snark.JobSummary` — the pure WorkItem-JSON peek
-- | that the P2P worker peer renders as its UI label. Runs in Node (no browser, no
-- | SRS): we craft the encoded JSON with `writeJSON` (the same shape the worker
-- | decodes) using known `Vesta.ScalarField` hexes, and assert the summary + label.
module Test.Snarky.Example.Snark.JobSummarySpec
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import JS.BigInt as BigInt
import Simple.JSON (writeJSON)
import Snarky.Curves.Class (fromBigInt, toHexLe)
import Snarky.Curves.Vesta as Vesta
import Snarky.Example.Snark.JobSummary (JobSummary(..), describeJob, fieldToDec, jobSummary, shortHex, transition)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | The little-endian hex of a small field value (how a WorkItem field serializes).
field :: Int -> String
field n = toHexLe (fromBigInt (BigInt.fromInt n) :: Vesta.ScalarField)

-- | A base WorkItem's encoded JSON, in the shape `jobSummary` decodes.
baseJSON :: { amount :: String, to :: String, source :: String, target :: String } -> String
baseJSON r = writeJSON
  { tag: "base"
  , base:
      { statement: { source: r.source, target: r.target }
      , tx: { transaction: { transfer: { to: { x: r.to }, amount: r.amount } } }
      }
  }

-- | A merge WorkItem's encoded JSON: `merge` is itself a JSON string carrying the
-- | merged statement (the child proofs, which need the SRS, are not peeked).
mergeJSON :: { source :: String, target :: String } -> String
mergeJSON stmt = writeJSON { tag: "merge", merge: writeJSON { statement: stmt } }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Snarky.Example.Snark.JobSummary" do
  describe "fieldToDec" do
    it "renders a little-endian field hex as its decimal value" do
      fieldToDec (field 0) `shouldEqual` "0"
      fieldToDec (field 100) `shouldEqual` "100"
      fieldToDec (toHexLe (fromBigInt (BigInt.fromInt 123456789) :: Vesta.ScalarField))
        `shouldEqual` "123456789"

  describe "jobSummary / describeJob" do
    it "summarizes a base job: transfer amount + recipient + ledger transition" do
      let
        amount = field 100
        to = field 7
        source = field 1
        target = field 2
        stmt = { source, target }
        json = baseJSON { amount, to, source, target }
      describeJob json `shouldEqual`
        ("base · transfer 100 → " <> shortHex to <> " · ledger " <> transition stmt)
      case jobSummary json of
        BaseJob b -> do
          fieldToDec b.amount `shouldEqual` "100"
          b.to `shouldEqual` to
          b.transition `shouldEqual` stmt
        _ -> fail "expected a BaseJob"

    it "summarizes a merge job: only the merged ledger transition" do
      let
        stmt = { source: field 3, target: field 9 }
        json = mergeJSON stmt
      describeJob json `shouldEqual` ("merge · ledger " <> transition stmt)
      case jobSummary json of
        MergeJob s -> s `shouldEqual` stmt
        _ -> fail "expected a MergeJob"

    it "falls back to the tag when a recognized job can't be peeked further" do
      -- a "base"-tagged item missing its `base` payload
      describeJob (writeJSON { tag: "base" }) `shouldEqual` "base"
      case jobSummary (writeJSON { tag: "base" }) of
        OtherJob t -> t `shouldEqual` "base"
        _ -> fail "expected OtherJob \"base\""

    it "labels an unknown tag / non-JSON as a generic job" do
      describeJob (writeJSON { tag: "deposit" }) `shouldEqual` "job"
      describeJob "not json at all" `shouldEqual` "job"
