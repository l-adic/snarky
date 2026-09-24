-- | The negative path of `compileMulti`'s structural validation: a
-- | compile-time parameter the caller declares, `@stepChunks`, is
-- | checked against what the circuit needs, and disagreement is an
-- | error that names both numbers.
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
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception as Exc
import Pickles (RuleEntry, StepField, compileMulti, mkRuleEntry)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (NrrRules, nrrRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (fail)

-- | Compiles `nrrRule`, the smallest rule available, at
-- | `@stepChunks = 2`. Its step domain is far below the 16 step IPA
-- | rounds, so the branch needs one chunk and the compile must throw.
spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.Compile.validateNumChunks" do
  it "throws when @stepChunks=2 but the circuit only needs 1" \{ pallasSrs, vestaSrs } -> do
    nrrEntry :: RuleEntry _ _ _ _ Unit _ _ <-
      liftEffect $ mkRuleEntry @0 @(F StepField) nrrRule Vector.nil
    let rules = tuple1 nrrEntry
    result <- withSpan "[CompileValidation] compile" $ liftEffect $ Exc.try $ compileMulti
      @NrrRules
      @(F StepField)
      @2
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: Nothing
      , lagrangeCache: Nothing
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
