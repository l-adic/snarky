-- | The negative path of the compiler's structural validation: a
-- | compile-time parameter the caller declares, `@stepChunks` or a
-- | slot's width, is checked against what the circuit or the slot's
-- | source needs, and disagreement is an error that names both
-- | numbers.
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
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception as Exc
import Pickles (RuleEntry, SlotWrapKey(..), StepField, compileMulti, mkRuleEntry)
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (nrrRule)
import Test.Pickles.Prove.TreeProofReturn (treeProofReturnRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (fail)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = do
  numChunksSpec
  slotWidthsSpec

-- | Compiles `nrrRule`, the smallest rule available, at
-- | `@stepChunks = 2`. Its step domain is far below the 16 step IPA
-- | rounds, so the branch needs one chunk and the compile must throw.
numChunksSpec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
numChunksSpec = describe "Pickles.Prove.Compile.validateNumChunks" do
  it "throws when @stepChunks=2 but the circuit only needs 1" \{ pallasSrs, vestaSrs } -> do
    nrrEntry :: RuleEntry _ _ _ _ Unit _ <-
      liftEffect $ mkRuleEntry @(F StepField) nrrRule Vector.nil
    let rules = tuple1 nrrEntry
    result <- withSpan "[CompileValidation] compile" $ liftEffect $ Exc.try $ compileMulti
      @(F StepField)
      @2
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: Nothing
      , lagrangeCache: Nothing
      , dump: Nothing
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

-- | `treeProofReturnRule` declares slot 0 at width 0 and slot 1 at
-- | width 2, in a tag with two slots. Built with keys that disagree,
-- | the entry must throw before any compile.
slotWidthsSpec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
slotWidthsSpec = describe "Pickles.Prove.Compile.requireSlotWidths" do
  it "throws when a Self slot's width is not the tag's" \_ -> do
    result :: Either Exc.Error (RuleEntry _ _ 2 _ Unit _) <- liftEffect $ Exc.try $
      mkRuleEntry @(F StepField) @() treeProofReturnRule (Self :< Self :< Vector.nil)
    expectWidthError "slot 0 declares width 0, but its source verifies 2" result

  it "throws when an External slot's width is not its source's" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    nrrEntry :: RuleEntry _ _ _ _ Unit _ <-
      liftEffect $ mkRuleEntry @(F StepField) nrrRule Vector.nil
    nrr <- withSpan "[CompileValidation] compile nrr" $ liftEffect $ compileMulti
      @(F StepField)
      @1
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: Nothing
      , lagrangeCache: Just lagrangeCache
      , dump: Nothing
      }
      (tuple1 nrrEntry)
    result :: Either Exc.Error (RuleEntry _ _ 2 _ Unit _) <- liftEffect $ Exc.try $
      mkRuleEntry @(F StepField) @() treeProofReturnRule
        (External nrr.tagData :< External nrr.tagData :< Vector.nil)
    expectWidthError "slot 1 declares width 2, but its source verifies 0" result

-- | Fails unless `result` is an error containing `expected`.
expectWidthError :: forall a. String -> Either Exc.Error a -> LoggerT Message Aff Unit
expectWidthError expected = case _ of
  Right _ -> fail $ "expected mkRuleEntry to throw: " <> expected
  Left err ->
    when (not (contains (Pattern expected) (Exc.message err)))
      $ fail
      $ "error did not mention '" <> expected <> "': " <> Exc.message err
