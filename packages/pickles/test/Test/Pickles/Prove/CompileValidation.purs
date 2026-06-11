-- | Negative-path tests for `compileMulti`'s structural validation
-- | checks. These confirm that the user-declared compile-time
-- | parameters (currently just `@stepChunks`) are validated against
-- | what the actual circuit needs, with a clear error message when
-- | they disagree.
module Test.Pickles.Prove.CompileValidation
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.String (contains)
import Data.String.Pattern (Pattern(..))
import Data.Tuple.Nested (tuple1)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception as Exc
import Pickles (NoSlots, RuleEntry, StepField, compileMulti, mkRuleEntry)
import Run as Run
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (NrrRules, nrrRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (fail)

-- | Re-uses the `Test.Pickles.Prove.NoRecursionReturn` rule (smallest
-- | available — N=0, no prev slots, ~447 gate step CS) and tries to
-- | compile it with `@stepChunks = 2`. Since the step domain log2 for
-- | this tiny rule is well below `StepIPARounds = 16`, the per-branch
-- | num_chunks is 1, and the validation must throw.
spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.Compile.validateNumChunks" do
  it "throws when @stepChunks=2 but the circuit only needs 1" \{ pallasSrs, vestaSrs } -> do
    nrrEntry :: RuleEntry _ _ _ _ _ Unit _ _ _ _ _ _ <-
      liftEffect $ mkRuleEntry @0 @(F StepField) @Unit @1 @1 nrrRule unit
    let rules = tuple1 nrrEntry
    result <- withSpan "[CompileValidation] compile" $ liftEffect $ Exc.try $ Run.runBaseEffect $ compileMulti
      @NrrRules
      @(F StepField)
      @Unit
      @NoSlots
      @2
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: Nothing
      }
      rules
    case result of
      Right _ ->
        fail "expected compileMulti to throw NumChunksMismatch (declared 2, actual 1)"
      Left err -> do
        let msg = Exc.message err
        when (not (contains (Pattern "declared stepChunks=2") msg))
          $ fail
          $ "error did not mention 'declared stepChunks=2': " <> msg
        when (not (contains (Pattern "num_chunks=1") msg))
          $ fail
          $ "error did not mention computed 'num_chunks=1': " <> msg
