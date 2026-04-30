-- | PureScript-side analog of OCaml's `No_recursion_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:100-126`).
-- |
-- | The simplest pickles rule: `max_proofs_verified = N0`, no prevs,
-- | Output mode (input = Unit, output = Field), constant output `0`.
-- | Exercised here via the `Pickles.Prove.CompileMulti` API end-to-end:
-- | a 1-rule carrier dispatched through `compileMulti` returns one
-- | `BranchProver`; one invocation produces a single proof; `verify`
-- | checks it.
-- |
-- | `nrrRule` is exported because `Test.Pickles.Verify.ExpandDeferredEq`
-- | reuses it to build a real NRR `CompiledProof` and feed
-- | `compiledProof.wrapDv` / `wrapDvInput` to its self-consistency check.
module Test.Pickles.Prove.NoRecursionReturn
  ( nrrRule
  , spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Pickles.Prove.CompileMulti
  ( BranchProver(..)
  , RulesCons
  , RulesNil
  , compileMulti
  , mkRuleEntry
  )
import Pickles.Prove.Step (StepRule)
import Pickles.Prove.Verify (verify)
import Pickles.Step.Prevs (PrevsSpecNil)
import Pickles.Types (StepField)
import Pickles.Wrap.Slots (NoSlots)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F, FVar, const_)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The NRR inductive rule — Output mode, N=0, returns `F zero`.
-- | Reference: `mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:100-107`.
nrrRule :: StepRule 0 Unit Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

-- | NRR's 1-rule carrier shape: a single `RulesCons` for the no-prev
-- | rule, terminated by `RulesNil`.
type NrrRules =
  RulesCons 0 Unit PrevsSpecNil Unit
    RulesNil

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.NoRecursionReturn" do
  it "compileMulti + prover.step end-to-end verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- Build the 1-tuple rules carrier for compileMulti. mpvMax = 0
    -- (NRR rule's mpv); since this is the only branch, nd = 1.
    -- outputSize = mpvMax*32 + 1 + mpvMax = 0 + 1 + 0 = 1.
    nrrEntry <- liftEffect $ mkRuleEntry
      @PrevsSpecNil
      @0 -- mpv (rule's own)
      @0 -- mpvMax (single rule, = mpv)
      @0 -- mpvPad
      @1 -- nd = topBranches (single branch)
      @1 -- outputSize
      @Unit
      @Unit
      @Unit
      @(F StepField)
      @(FVar StepField)
      @Unit
      @Unit
      @Unit
      nrrRule
      unit

    let rules = tuple1 nrrEntry

    output <- liftEffect $ compileMulti
      @NrrRules
      @Unit
      @(F StepField)
      @Unit
      @0
      @NoSlots
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      }
      rules

    let BranchProver nrrProver = fst output.provers
    eResult <- liftEffect $ runExceptT $ nrrProver { appInput: unit, prevs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("nrrProver: " <> show e)
      Right compiledProof ->
        verify output.verifier [ compiledProof ] `shouldEqual` true
