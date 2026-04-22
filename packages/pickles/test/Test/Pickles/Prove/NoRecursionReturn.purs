-- | PureScript-side analog of OCaml's `No_recursion_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:89-126` +
-- |  `mina/src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.ml`).
-- |
-- | Thin wrapper around `Test.Pickles.Prove.NoRecursionReturn.Producer`:
-- | sets up the SRS, emits the test's `begin`/`end` trace markers, and
-- | calls the producer. Asserts that the produced step + wrap proofs
-- | verify via `ProofFFI.verifyOpeningProof` (kimchi batch_verify).
-- |
-- | The producer also emits `[LABEL] VALUE` lines via `Pickles.Trace`
-- | for each intermediate value; those go to `PICKLES_TRACE_FILE`
-- | when set (no-op otherwise). The manual convergence tool
-- | `tools/no_recursion_return_trace_diff.sh` compares that output
-- | against the OCaml dumper's trace, but the test itself only cares
-- | about `batch_verify`.
-- |
-- | The same producer is reused from `Test.Pickles.Prove.TreeProofReturn`
-- | (Tree_proof_return verifies a No_recursion_return proof at slot 0
-- | of its base case).
-- |
-- | Required env vars at runtime:
-- | - `KIMCHI_DETERMINISTIC_SEED` — u64 seed for the patched kimchi RNG.
-- | - (optional) `PICKLES_TRACE_FILE` — trace log path; only for manual
-- |   convergence debugging.
-- | - (optional) `KIMCHI_WITNESS_DUMP=/tmp/nrr_%c.witness` — writes
-- |   kimchi witness matrices for `tools/no_recursion_return_witness_diff.sh`.
module Test.Pickles.Prove.NoRecursionReturn
  ( spec
  ) where

import Prelude

import Data.Int.Bits as Int
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Trace as Trace
import Pickles.Types (StepField)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)
import Test.Spec (SpecT, describe, it)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.NoRecursionReturn" do
  it "N=0 Output-mode proof: step + wrap verify via batch_verify" \_ -> do
    liftEffect $ Trace.string "no_recursion_return.begin" "base_case"
    let pallasWrapSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    _ <- produceNoRecursionReturn
      { vestaSrs
      , lagrangeSrs: pallasWrapSrs
      , pallasProofCrs: pallasWrapSrs
      }
    liftEffect $ Trace.string "no_recursion_return.end" "base_case_verified"
