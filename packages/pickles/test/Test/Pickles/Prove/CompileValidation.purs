-- | Negative-path tests for `compileMulti`'s structural validation
-- | checks. These confirm that the user-declared compile-time
-- | parameters (currently just `@numChunks`) are validated against
-- | what the actual circuit needs, with a clear error message when
-- | they disagree.
module Test.Pickles.Prove.CompileValidation
  ( spec
  ) where

import Prelude

import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Maybe (Maybe(..))
import Data.String (contains)
import Data.String.Pattern (Pattern(..))
import Data.Tuple.Nested (tuple1)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception as Exc
import Pickles (NoSlots, StepField, compileMulti, mkRuleEntry)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F)
import Test.Pickles.Prove.NoRecursionReturn (NrrRules, nrrRule)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (fail)

-- | Re-uses the `Test.Pickles.Prove.NoRecursionReturn` rule (smallest
-- | available — N=0, no prev slots, ~447 gate step CS) and tries to
-- | compile it with `@numChunks = 2`. Since the step domain log2 for
-- | this tiny rule is well below `StepIPARounds = 16`, the per-branch
-- | num_chunks is 1, and the validation must throw.
spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.Compile.validateNumChunks" do
  it "throws when @numChunks=2 but the circuit only needs 1" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField
    nrrEntry <- liftEffect $ mkRuleEntry @0 @(F StepField) @Unit @1 nrrRule unit
    let rules = tuple1 nrrEntry
    result <- liftEffect $ Exc.try $ compileMulti
      @NrrRules
      @(F StepField)
      @Unit
      @NoSlots
      @2
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      }
      rules
    case result of
      Right _ ->
        fail "expected compileMulti to throw NumChunksMismatch (declared 2, actual 1)"
      Left err -> do
        let msg = Exc.message err
        when (not (contains (Pattern "declared numChunks=2") msg))
          $ fail
          $ "error did not mention 'declared numChunks=2': " <> msg
        when (not (contains (Pattern "num_chunks=1") msg))
          $ fail
          $ "error did not mention computed 'num_chunks=1': " <> msg
