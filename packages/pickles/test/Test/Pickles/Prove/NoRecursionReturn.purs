-- | PureScript-side analog of OCaml's `No_recursion_return` test
-- | (`mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:100-126`).
-- |
-- | The simplest pickles rule: `max_proofs_verified = N0`, no prevs,
-- | Output mode (input = Unit, output = StepField), constant output `0`.
-- | Exercised here via the `Pickles.Prove.CompileMulti` API end-to-end:
-- | a 1-rule carrier dispatched through `compileMulti` returns one
-- | `BranchProver`; one invocation produces a single proof; `verify`
-- | checks it.
-- |
-- | `nrrRule` is exported because `Test.Pickles.Prove.CompileValidation`
-- | and `Test.Pickles.Sideload.DigestEqNrrSpec` reuse it to build a
-- | real NRR `CompiledProof`.
module Test.Pickles.Prove.NoRecursionReturn
  ( NrrRules
  , nrrRule
  , spec
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1)
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), NoSlots, RulesCons, RulesNil, StepField, StepRule, compileMulti, mkRuleEntry, toVerifiable, verify)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.DSL (F, FVar, const_)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The NRR inductive rule — Output mode, N=0, returns `F zero`.
-- | Reference: `mina/src/lib/crypto/pickles/test/test_no_sideloaded.ml:100-107`.
nrrRule :: StepRule 0 Unit Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

-- | NRR's 1-rule carrier shape: a single `RulesCons` for the no-prev
-- | rule, terminated by `RulesNil`.
type NrrRules =
  RulesCons 0 Unit Unit Unit
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.NoRecursionReturn" do
  it "compileMulti + prover.step end-to-end verify returns true" \{ pallasSrs, vestaSrs } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/NoRecursionReturn.json")

    -- Build the 1-tuple rules carrier for compileMulti. mpvMax = 0
    -- (NRR rule's mpv); since this is the only branch, nd = 1.
    -- outputSize = mpvMax*32 + 1 + mpvMax = 0 + 1 + 0 = 1.
    nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) @Unit @1 @1 nrrRule unit

    let rules = tuple1 nrrEntry

    logInfo "[NoRecursionReturn] compiling…"
    output <- withSpan "[NoRecursionReturn] compile" $ liftEffect $ compileMulti
      @NrrRules
      @(F StepField)
      @Unit
      @NoSlots
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      }
      rules

    let BranchProver nrrProver = fst output.provers
    -- Compiled-only spec (Unit) → spec-derived `vkCarrier =
    -- Unit`. Mirrors OCaml's `~handler:None` for non-side-loaded
    -- branches. Threading the field uniformly keeps the
    -- `BranchProver` API consistent with side-loaded specs.
    logInfo "[NoRecursionReturn] proving"
    eResult <- withSpan "[NoRecursionReturn] prove" $ liftEffect $ nrrProver noAdvice
      { appInput: unit, prevs: unit, sideloadedVKs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("nrrProver: " <> show e)
      Right compiledProof -> do
        logInfo "[NoRecursionReturn] verifying proof…"
        verify output.verifier (toVerifiable compiledProof) `shouldEqual` true
        logInfo "[NoRecursionReturn] verification complete"
