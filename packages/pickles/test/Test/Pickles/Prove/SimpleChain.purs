-- | PureScript-side analog of OCaml's `Simple_chain` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:128-205`).
-- |
-- | The OCaml runner at `mina/src/lib/crypto/pickles/dump_simple_chain/dump_simple_chain.exe`
-- | exercises the base case (b0) only, with deterministic ChaCha20Rng
-- | seeded from `KIMCHI_DETERMINISTIC_SEED`, and emits a trace file via
-- | `Pickles_trace`. The captured fixture lives at
-- | `packages/pickles/test/fixtures/simple_chain_base_case.trace`.
-- |
-- | This spec emits a matching trace from PureScript so the two trace files
-- | can be diffed to verify byte-identical pickles transcript reproduction.
-- |
-- | First iteration: the spec only emits the begin/end sentinels — the
-- | actual step proof construction lands in subsequent commits driven by
-- | the diff against the OCaml fixture. The loop works end-to-end (run
-- | OCaml dump → run PS spec → diff), so each iteration picks the topmost
-- | missing line in the diff and adds the matching PS code + trace point.
-- |
-- | Required env vars at runtime:
-- | - `PICKLES_TRACE_FILE` — path to the trace log (truncated). When unset,
-- |   every trace call is a no-op.
-- | - `KIMCHI_DETERMINISTIC_SEED` — u64 seed for the patched kimchi RNG.
-- |   Required (exits 1 if unset) for any code that creates a kimchi proof.
module Test.Pickles.Prove.SimpleChain
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Trace as Trace
import Test.Spec (SpecT, describe, it)

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SimpleChain" do
  it "base case trace matches OCaml fixture" \_ -> do
    -- Mirror OCaml dump_simple_chain.ml's begin sentinel at line 80.
    liftEffect $ Trace.string "simple_chain.begin" "base_case"
    -- TODO (driven by diff against fixture):
    --   1. Compile the Simple_chain rule (translation of OCaml inductive
    --      rule lines 149-171) via the PureScript Pickles compile path.
    --   2. Run the step solver for the base case (self = 0).
    --   3. Call vestaCreateProof with the resulting witness + prover index.
    --   4. After receiving the kimchi proof, walk public_inputs and emit
    --      `step.proof.public_input.{i}` for each — matching the trace
    --      point in mina/src/lib/crypto/pickles/step.ml around line 822.
    -- Each iteration of the diff loop unblocks one or more of these
    -- steps. The minimum "working" first iteration is: PS emits the
    -- begin/end sentinels + the diff command runs.
    liftEffect $ Trace.string "simple_chain.end" "base_case_verified"
