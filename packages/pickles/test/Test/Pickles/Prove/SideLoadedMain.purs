-- | M6 acceptance test for the side-loaded `step_main` plumbing.
-- |
-- | Drives `compileMulti` over a 1-rule spec whose single prev slot is a
-- | `PrevsSpecSideLoadedCons` (mirrors OCaml's
-- | `dump_side_loaded_main.ml:99-156` parent: side-loaded child verifier
-- | with `Width.Max = N2`). Re-uses `simpleChainRule` from
-- | `Test.Pickles.Prove.SimpleChain` — the rule body is identical, the
-- | only spec-level difference is that the prev slot's wrap key is
-- | side-loaded (handler-provided) instead of compile-time-known.
-- |
-- | Acceptance criterion (the M6 milestone): `compileMulti` returns a
-- | `BranchProver` closure without crashing. Prove-time invocation is
-- | M7+; this test does NOT call the prover.
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

    -- Project the single branch's prover. The newtype unwrap forces
    -- the closure into scope; if `compileMulti` had crashed (e.g. on
    -- a missing `MkUnitVkCarrier` instance for the side-loaded
    -- carrier shape), we'd never have reached this point.
    let BranchProver _chainProver = fst output.provers
    -- M6 sanity: the compile pipeline ran end-to-end and produced a
    -- BranchProver. Prove-time invocation is M7+.
    true `shouldEqual` true
