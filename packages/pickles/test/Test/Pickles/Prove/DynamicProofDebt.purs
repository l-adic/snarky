-- | One compiled incrementer evaluates an alternating sequence before any
-- | proof is requested. Proof debt is discharged from retained witnesses.
module Test.Pickles.Prove.DynamicProofDebt (spec) where

import Prelude

import Colog (LoggerT, Message, logInfo)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (foldM)
import Data.Maybe (Maybe(..))
import Data.String (contains)
import Data.String.Pattern (Pattern(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Pickles (ApplicationStatement(..), CompiledProof(..), PrevStatement(..), ProveError, Slot, SlotWrapKey(..), StepField, StepRule, compileMulti, deferredPrev, deferredStatement, evaluateBranch, mkRuleEntry, prevValues, proveDeferred, provedPrev, toPrevs, toVerifiable, unprovedPrev, verify)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.Proof (vestaProofToSerdeJson)
import Snarky.Circuit.CVar (add_)
import Snarky.Circuit.DSL (F(..), FVar, const_, exists)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.Outputs (appOutputs)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type Statement = ApplicationStatement Unit (F StepField)
type Prevs = Tuple1 (Slot 1 Statement)

incrementRule
  :: Ref Boolean
  -> Ref Int
  -> StepRule Prevs Unit Unit (F StepField) (FVar StepField)
incrementRule advice ruleEvaluations getPrevs _ = do
  previous <- exists $ getPrevs <#> prevValues <#> \(s /\ _) -> s
  mustVerify <- exists $ liftEffect $ Ref.read advice
  _ :: Unit <- exists $ liftEffect $ Ref.modify_ (_ + 1) ruleEvaluations
  let ApplicationStatement { output: counter } = previous
  pure
    { prevs: toPrevs $ PrevStatement { publicInput: previous, proofMustVerify: mustVerify } /\ unit
    , publicOutput: add_ counter (const_ one)
    }

statement :: Int -> Statement
statement counter = ApplicationStatement { input: unit, output: F (fromInt counter) }

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.DynamicProofDebt" do
  it "evaluates once and resolves deferred proofs only when the rule requires them" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    outputs <- liftEffect $ appOutputs "DynamicProofDebt"
    mustVerify <- liftEffect $ Ref.new false
    ruleEvaluations <- liftEffect $ Ref.new 0
    entry <- liftEffect $ mkRuleEntry @(F StepField) (incrementRule mustVerify ruleEvaluations) (Self :< Vector.nil)
    logInfo "[DynamicProofDebt] compiling incrementer once…"
    app <- liftEffect $ compileMulti @(F StepField) @1
      { srs: { vestaSrs, pallasSrs }
      , debug: true
      , wrapDomainOverride: Nothing
      , proofCache: outputs.proofCache
      , lagrangeCache: Just lagrangeCache
      , dump: outputs.dumpAt "incrementer"
      }
      (tuple1 entry)
    liftEffect (Ref.read ruleEvaluations) >>= (_ `shouldEqual` 0)
    let
      branch = fst app.provers
      evaluate required prev = do
        Ref.write required mustVerify
        evaluateBranch branch noAdvice { appInput: unit, prevs: tuple1 prev } >>= expectRight
      checkProof counter proof@(CompiledProof raw) = do
        liftEffect $ assertStatement counter raw.statement
        verify app.verifier (toVerifiable proof) `shouldEqual` true

    -- Evaluation obtains all four statements without resolving any debt.
    invocations <- foldM
      ( \previous iteration -> do
          let
            prev = case Array.last previous of
              Nothing -> unprovedPrev (statement 0)
              Just pending -> deferredPrev pending
          pending <- liftEffect $ evaluate (iteration `mod` 2 == 0) prev
          liftEffect $ assertStatement iteration (deferredStatement pending)
          pure (Array.snoc previous pending)
      )
      []
      [ 1, 2, 3, 4 ]
    liftEffect (Ref.read ruleEvaluations) >>= (_ `shouldEqual` 4)
    case invocations of
      [ _, second, _, fourth ] -> do
        -- Later advice changes cannot change the already evaluated flag.
        liftEffect $ Ref.write false mustVerify
        finalProof <- liftEffect $ proveDeferred fourth >>= expectRight
        checkProof 4 finalProof
        secondProof <- liftEffect $ proveDeferred second >>= expectRight
        checkProof 2 secondProof
        repeated <- liftEffect $ proveDeferred fourth >>= expectRight
        let
          CompiledProof original = finalProof
          CompiledProof cached = repeated
        vestaProofToSerdeJson cached.wrapProof `shouldEqual` vestaProofToSerdeJson original.wrapProof
        liftEffect (Ref.read ruleEvaluations) >>= (_ `shouldEqual` 4)

        -- A deferred invocation with missing debt still yields its statement.
        missing <- liftEffect $ evaluate true (unprovedPrev (statement 4))
        liftEffect $ assertStatement 5 (deferredStatement missing)
        skipped <- liftEffect $ evaluate false (deferredPrev missing)
        skippedProof <- liftEffect $ proveDeferred skipped >>= expectRight
        checkProof 6 skippedProof
        liftEffect (Ref.read ruleEvaluations) >>= (_ `shouldEqual` 6)
        liftEffect $ proveDeferred missing >>= expectFailure "required proof is missing"
        liftEffect $ proveDeferred missing >>= expectFailure "branch 0 slot 0"

        -- The same missing debt is required by a subsequent true flag.
        required <- liftEffect $ evaluate true (deferredPrev missing)
        liftEffect $ proveDeferred required >>= expectFailure "required proof is missing"
        liftEffect (Ref.read ruleEvaluations) >>= (_ `shouldEqual` 7)

        let
          CompiledProof raw = secondProof
          badDomain = CompiledProof (raw { stepDomainLog2 = 30 })
          forged = CompiledProof (raw { statement = statement 9 })
        incompatible <- liftEffect $ evaluate true (provedPrev badDomain)
        liftEffect $ proveDeferred incompatible >>= expectFailure "proof step domain is not a branch"
        forgedStatement <- liftEffect $ evaluate true (provedPrev forged)
        liftEffect $ proveDeferred forgedStatement >>= expectFailure "FailedAssertion"
        liftEffect (Ref.read ruleEvaluations) >>= (_ `shouldEqual` 9)
      _ -> liftEffect $ throw "expected four incrementer evaluations"

assertStatement :: Int -> Statement -> Effect Unit
assertStatement counter (ApplicationStatement actual) =
  unless (actual.output == F (fromInt counter)) $
    throw ("expected counter " <> show counter <> ", got " <> show actual.output)

expectRight :: forall a. Either ProveError a -> Effect a
expectRight = case _ of
  Left e -> throw (show e)
  Right p -> pure p

expectFailure :: forall a. String -> Either ProveError a -> Effect Unit
expectFailure expected = case _ of
  Right _ -> throw ("expected failure containing: " <> expected)
  Left e -> unless (contains (Pattern expected) (show e)) $ throw (show e)
