-- | M6 / M7a acceptance test for the side-loaded `step_main` plumbing.
-- |
-- | Drives `compileMulti` over a 1-rule spec whose single prev slot is a
-- | `PrevsSpecSideLoadedCons` (mirrors OCaml's
-- | `dump_side_loaded_main.ml:99-156` parent: side-loaded child verifier
-- | with `Width.Max = N2`). Re-uses `simpleChainRule` from
-- | `Test.Pickles.Prove.SimpleChain` — the rule body is identical, the
-- | only spec-level difference is that the prev slot's wrap key is
-- | side-loaded (handler-provided) instead of compile-time-known.
-- |
-- | M6: `compileMulti` returns a `BranchProver` closure without
-- |   crashing — the typeclass-driven pipeline accepts a side-loaded
-- |   prevsSpec at compile time.
-- |
-- | M7a (the just-landed step): the per-prove `sideloadedVKs` channel
-- |   on `StepInputs` / `BranchProver` is plumbed end-to-end. The 4
-- |   pre-existing tests (NRR / Simple_chain / Tree_proof_return /
-- |   Two_phase_chain) regression-confirm that compiled-only specs
-- |   thread `mkUnitVkCarrier` placeholders through unchanged.
-- |
-- |   The side-loaded slot has NO `BasePrev` path: OCaml's analog
-- |   `dump_side_loaded_main.ml:190-202` always passes a real child
-- |   proof at prove time (`No_recursion.example_proof` wrapped via
-- |   `Side_loaded.Proof.of_proof` to lift the actual width N0 into
-- |   the side-loaded tag's bound N2). Driving the parent prover
-- |   therefore requires an `InductivePrev` carrying a width-lifted
-- |   child `CompiledProof 2 …`.
-- |
-- | M7b/M9 (next): produce a child `CompiledProof 0 (StatementIO Field
-- |   Unit) Unit Unit` PS-side (Input-mode No_recursion asserting
-- |   `self == 0`) — or load the OCaml fixture at
-- |   `packages/pickles/test/fixtures/sideload_main_child/` — then
-- |   width-lift it to `CompiledProof 2 …` (the side-loaded slot's
-- |   compile-time bound) by repacking the existential `widthData`.
-- |   Drive the parent prover, dump the witness via
-- |   `KIMCHI_WITNESS_DUMP`, diff against committed
-- |   `ocaml_main_step_b1.txt` via `tools/witness_diff.sh`.
-- |
-- | Reference: `docs/sideload-witness-loop-handoff.md`.
module Test.Pickles.Prove.SideLoadedMain
  ( spec
  ) where

import Prelude

import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Pickles.Prove.Compile
  ( BranchProver(..)
  , RulesCons
  , RulesNil
  , compileMulti
  , mkRuleEntry
  )
import Pickles.Step.Prevs (PrevsSpecNil, PrevsSpecSideLoadedCons)
import Pickles.Types (StatementIO, StepField)
import Pickles.Wrap.Slots (Slots1)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.SimpleChain (simpleChainRule)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | Single-rule spec: one self-recursive rule whose prev slot is
-- | side-loaded with `Width.Max = N2`. Mirrors OCaml
-- | `dump_side_loaded_main.ml`'s parent step rule.
-- |
-- | * outer rule mpv = 1 (one prev slot)
-- | * prev slot's compile-time width upper bound = 2
-- | * `Tuple1 Unit` slotVKs: side-loaded slots have NO compile-time
-- |   wrap key (the head entry is `Unit` per the
-- |   `PrevsSpecSideLoadedCons` `CompilableSpec` instance).
type SideLoadedMainRules =
  RulesCons 1
    (Tuple1 (StatementIO (F StepField) Unit))
    (PrevsSpecSideLoadedCons 2 (StatementIO (F StepField) Unit) PrevsSpecNil)
    (Tuple1 Unit)
    RulesNil

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.SideLoadedMain" do
  it "compileMulti type-checks + returns a BranchProver for a side-loaded spec" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- Single-rule entry. mpvMax=1 (one prev slot at the outer rule),
    -- outputVal=Unit, prevInputVal=F StepField — same as Simple_chain.
    -- `tuple1 unit` is the side-loaded slot's empty compile-time wrap
    -- key carrier.
    sideLoadedEntry <- liftEffect $ mkRuleEntry
      @1
      @Unit
      @(F StepField)
      simpleChainRule
      (tuple1 unit)

    let rules = tuple1 sideLoadedEntry

    output <- liftEffect $ compileMulti
      @SideLoadedMainRules
      @Unit
      @(F StepField)
      @(Slots1 2)
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      }
      rules

    -- M6/M7a sanity: `compileMulti`'s side-loaded plumbing produced a
    -- `BranchProver`. The newtype unwrap forces the closure into
    -- scope. Prove-time invocation requires an `InductivePrev` whose
    -- `CompiledProof 2 …` is width-lifted from a real child proof
    -- (OCaml `Side_loaded.Proof.of_proof` analog). That bridge is
    -- M7b — see `docs/sideload-witness-loop-handoff.md`.
    let BranchProver _chainProver = fst output.provers
    true `shouldEqual` true
