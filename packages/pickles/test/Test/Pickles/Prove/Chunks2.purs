-- | The chunked case: one rule with no prevs whose body fills 2^16
-- | rows, declared at `stepChunks = 2` with the wrap domain overridden
-- | to 2^14, so kimchi's PCS runs the step at two chunks and the wrap
-- | at one.
-- |
-- | Proving emits a step and a wrap kimchi witness — counters 0 and 1
-- | under `KIMCHI_WITNESS_DUMP` — which a byte-for-byte diff against
-- | the reference dump compares.
module Test.Pickles.Prove.Chunks2
  ( Chunks2Rules
  , chunks2Rule
  , spec
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Either (Either(..))
import Data.Int.Bits as Bits
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), RulesCons, RulesNil, StepField, StepRule, compileMulti, mkRuleEntry, toPrevs, toVerifiable, verify)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.DSL (F, addConstraint, exists, mul_)
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | 2^17 + 1 `mul_` fillers on fresh zeros — each constraint is half a
-- | kimchi row, so 2^16 + 1 rows — then one 7-wire Raw Generic with
-- | zero coefficients, which pushes the 7th permuted column's degree
-- | above 2^16.
chunks2Rule :: StepRule Unit Unit Unit Unit Unit
chunks2Rule _ _ = do
  let
    freshZero = exists (pure (zero :: F StepField))
    iters = (1 `Bits.shl` 17) + 1
    mulOne = do
      z1 <- freshZero
      z2 <- freshZero
      _ <- mul_ z1 z2
      pure unit
  tailRecM
    ( \i ->
        if i >= iters then pure (Done unit)
        else mulOne *> pure (Loop (i + 1))
    )
    0
  z <- freshZero
  addConstraint $ KimchiPad
    (z :< z :< z :< z :< z :< z :< z :< Vector.nil)
  pure
    { prevs: toPrevs unit
    , publicOutput: unit
    }

-- | Carrier for the single `chunks2Rule`, at width 0 with no prevs.
type Chunks2Rules =
  RulesCons 0 Unit
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.Chunks2" do
  it "base case (b0) — chunks=2 step+wrap proves end-to-end" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/Chunks2.json")

    -- The step SRS has depth 2^16, and this rule's 2^16 rows round the
    -- step domain up to 2^17, giving two chunks. The wrap SRS has depth
    -- 2^15 and the wrap domain is overridden to 2^14, giving one chunk
    -- and a `max_poly_size` of 32768.
    chunks2Entry <- liftEffect $ mkRuleEntry @0 @Unit chunks2Rule Vector.nil
    let rules = tuple1 chunks2Entry

    logInfo "[Chunks2] compiling…"
    output <- withSpan "[Chunks2] compile" $ liftEffect $ compileMulti
      @Chunks2Rules
      @Unit
      @2
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Just 14
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      rules

    let BranchProver chunks2Prover = fst output.provers
    logInfo "[Chunks2] proving"
    eResult <- withSpan "[Chunks2] prove" $ liftEffect $ chunks2Prover noAdvice
      { appInput: unit, prevs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("chunks2Prover: " <> show e)
      Right compiledProof -> do
        logInfo "[Chunks2] verifying proof…"
        verify output.verifier (toVerifiable compiledProof) `shouldEqual` true
        logInfo "[Chunks2] verification complete"
