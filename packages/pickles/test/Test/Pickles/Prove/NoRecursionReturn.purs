-- | PureScript-side analog of OCaml's `No_recursion_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:89-126` +
-- |  `mina/src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.ml`).
-- |
-- | Thin wrapper around `Test.Pickles.Prove.NoRecursionReturn.Producer`:
-- | sets up the SRS, emits the test's `begin`/`end` trace markers, and
-- | calls the producer. The producer emits all `compile.*` VK blocks,
-- | `step.proof.public_input.*`, `wrap.witness.{col0,pi}.*`, and
-- | `wrap.proof.opening.*` lines verbatim with the OCaml fixture at
-- | `packages/pickles/test/fixtures/no_recursion_return_base_case.trace`.
-- |
-- | The same producer is reused from `Test.Pickles.Prove.TreeProofReturn`
-- | (Tree_proof_return verifies a No_recursion_return proof at slot 0 of
-- | its base case).
-- |
-- | Required env vars at runtime:
-- | - `PICKLES_TRACE_FILE`       — trace log path (truncated).
-- | - `KIMCHI_DETERMINISTIC_SEED` — u64 seed for the patched kimchi RNG.
-- | - (optional) `KIMCHI_WITNESS_DUMP=/tmp/nrr_%c.witness` — for Rust-level
-- |   witness matrix equality check (see `tools/no_recursion_return_witness_diff.sh`).
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
  it "single N=0 Output-mode proof trace matches OCaml fixture" \_ -> do
    liftEffect $ Trace.string "no_recursion_return.begin" "base_case"
    let pallasWrapSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    _ <- produceNoRecursionReturn
      { vestaSrs
      , lagrangeSrs: pallasWrapSrs
      , pallasProofCrs: pallasWrapSrs
      }
    liftEffect $ Trace.string "no_recursion_return.end" "base_case_verified"
