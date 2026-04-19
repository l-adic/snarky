-- | PureScript-side analog of OCaml's `No_recursion_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:89-126` +
-- |  `mina/src/lib/crypto/pickles/dump_no_recursion_return/dump_no_recursion_return.ml`).
-- |
-- | Runs the same N=0 Output-mode rule (`public_output = 0`, no prev
-- | proofs) through the PS step+wrap prover and emits a trace that
-- | should byte-identical-match the OCaml fixture at
-- | `packages/pickles/test/fixtures/no_recursion_return_base_case.trace`
-- | via `tools/no_recursion_return_trace_diff.sh`.
-- |
-- | This is the simplest possible proof-level test — N=0 means no
-- | prev proofs, no verify_one, no heterogeneous advice. The trace
-- | contains only compile.* (stepVK+wrapVK), step.* (one step proof),
-- | wrap.* (one wrap proof), step_main_outer.* (outer-hash sponge),
-- | ivp.* (in-circuit IVP checks), ipa.* (IPA rounds) and the
-- | begin/end markers — no `expand_proof.*` / `msgForNextStep.*` /
-- | `tock_pi.*` since there's no prev proof to run oracles on or
-- | hash into messages_for_next_step_proof.
-- |
-- | This is the FIRST rung of the Tree_proof_return proof-level
-- | ladder: once this converges, we have a PS No_recursion_return
-- | prover that can produce slot-0 proofs for Tree_proof_return.
-- |
-- | Required env vars at runtime:
-- | - `PICKLES_TRACE_FILE` — path to the trace log (truncated).
-- | - `KIMCHI_DETERMINISTIC_SEED` — u64 seed for the patched kimchi RNG.
module Test.Pickles.Prove.NoRecursionReturn
  ( spec
  ) where

import Prelude

import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Trace as Trace
import Test.Spec (SpecT, describe, it)

-- | The loop entry point. Initial skeleton emits only the begin/end
-- | markers — iterations of `tools/no_recursion_return_trace_diff.sh`
-- | will drive filling in the middle (compile, step prove, wrap
-- | prove) one divergence at a time.
spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.NoRecursionReturn" do
  it "single N=0 Output-mode proof trace matches OCaml fixture" \_ -> do
    liftEffect $ Trace.string "no_recursion_return.begin" "base_case"
    -- TODO(iteration-1): compile No_recursion_return step+wrap, emit
    --   compile.stepVK.* / compile.wrapVK.* / compile.step_domains.* /
    --   compile.wrap_domains.* / compile.wrapCS.* entries (see OCaml
    --   fixture lines 2-237 for target).
    -- TODO(iteration-2): run step prover, emit step.* entries.
    -- TODO(iteration-3): run wrap prover, emit wrap.* /
    --   step_main_outer.* / ivp.* / ipa.* entries.
    liftEffect $ Trace.string "no_recursion_return.end" "base_case_verified"
