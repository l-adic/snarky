module Test.Pickles.Prove.DynamicProofDebt (spec) where

import Prelude

import Colog (LoggerT, Message)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1)
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Pickles (ApplicationStatement(..), BranchProver(..), CompiledProof(..), PrevStatement(..), Slot, SlotWrapKey(..), StepField, StepRule, compileMulti, initialStatement, mkRuleEntry, prevValues, proofRef, proofStatement, toPrevs, toVerifiable, verify)
import Pickles.Prove.Step (ruleDemands)
import Pickles.VerificationKey (verifierIndexDigest)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.CVar (add_)
import Snarky.Circuit.DSL (BoolVar, F(..), FVar, const_, exists, valueToFields)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type Statement = ApplicationStatement Boolean (F StepField)

type IncrementPrevs = Tuple1 (Slot 1 Statement)

-- | Increment the previous output. The Boolean input is ordinary rule
-- | advice and becomes the slot's proof debt directly. The zero-field
-- | witness action counts runtime rule executions, including child rules.
incrementRule
  :: Ref Int
  -> StepRule IncrementPrevs Boolean (BoolVar StepField) (F StepField) (FVar StepField)
incrementRule executions getPrev mustVerify = do
  _ :: Unit <- exists $ liftEffect $ Ref.modify_ (_ + 1) executions
  previous@(ApplicationStatement state) <- exists (getPrev <#> prevValues <#> fst)
  pure
    { prevs: toPrevs $ tuple1 $ PrevStatement
        { publicInput: previous
        , proofMustVerify: mustVerify
        }
    , publicOutput: add_ state.output (const_ one)
    }

statement :: Boolean -> Int -> Statement
statement required output = ApplicationStatement { input: required, output: F (fromInt output) }

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.DynamicProofDebt" do
  -- The rule body alone yields the requests the full solve prepares
  -- from, without a compiled circuit or any child proof.
  it "reads the rule's proof debt without proving"
    \_ -> do
      executions <- liftEffect $ Ref.new 0
      let
        demands required previous = do
          result <- liftEffect $
            ruleDemands @IncrementPrevs @Boolean @(BoolVar StepField) @(F StepField) @(FVar StepField)
              noAdvice
              { debug: true }
              (incrementRule executions)
              { publicInput: required, prevAppStates: tuple1 previous }
          case result of
            Left e -> liftEffect $ throw (show e)
            Right requests -> pure (Vector.toUnfoldable requests :: Array _)
      demands true (statement false 1) >>= shouldEqual
        [ { statement: valueToFields @StepField (statement false 1), mustVerify: true } ]
      demands false (statement true 2) >>= shouldEqual
        [ { statement: valueToFields @StepField (statement true 2), mustVerify: false } ]
      liftEffect (Ref.read executions) >>= (_ `shouldEqual` 2)

  -- One scenario compiles the application once and shares it across all
  -- demand and cache checks. SRS setup remains the suite's beforeAll hook.
  it "skips debt on an odd iteration and reuses a child proof on even iterations"
    \{ pallasSrs, vestaSrs, lagrangeCache } -> do
      executions <- liftEffect $ Ref.new 0
      childInvocations <- liftEffect $ Ref.new 0
      entry <- liftEffect $ mkRuleEntry @(F StepField) (incrementRule executions) (Self :< Vector.nil)
      compiled <- liftEffect $ compileMulti @(F StepField) @1
        { srs: { pallasSrs, vestaSrs }
        , debug: true
        , wrapDomainOverride: Nothing
        , proofCache: Nothing
        , lagrangeCache: Just lagrangeCache
        , dump: Nothing
        }
        (tuple1 entry)
      let
        prover@(BranchProver { prove, demands }) = fst compiled.provers
        childProver = BranchProver
          { prove: \handler input -> do
              Ref.modify_ (_ + 1) childInvocations
              prove handler input
          , demands
          }

        proveParent required previous expected = do
          result <- liftEffect $ prove noAdvice { appInput: required, prevs: tuple1 previous }
          proof <- case result of
            Left e -> liftEffect $ throw (show e)
            Right p -> pure p
          let CompiledProof { statement: ApplicationStatement actual } = proof
          actual.input `shouldEqual` required
          actual.output `shouldEqual` F (fromInt expected :: StepField)
          verify compiled.verifier (toVerifiable proof) `shouldEqual` true

      first <- liftEffect $ proofRef childProver noAdvice
        { statement: statement false 1
        , prevs: tuple1 (initialStatement (statement false 0))
        }
      second <- liftEffect $ proofRef prover noAdvice
        { statement: statement true 2
        , prevs: tuple1 first
        }
      let ApplicationStatement claim = proofStatement second
      claim.output `shouldEqual` F (fromInt 2 :: StepField)
      liftEffect (Ref.read executions) >>= (_ `shouldEqual` 0)

      -- The pre-flight names the proof the solve will demand, with the
      -- key it must be of, from a statement alone: the rule body runs
      -- once, no child is invoked.
      preflight <- liftEffect $ demands noAdvice
        { appInput: true, prevs: tuple1 (initialStatement (statement false 1)) }
      case preflight of
        Right [ demanded ] -> do
          demanded.statement `shouldEqual` valueToFields @StepField (statement false 1)
          demanded.mustVerify `shouldEqual` true
          verifierIndexDigest demanded.wrapVK `shouldEqual`
            verifierIndexDigest compiled.vks.wrap.verifierIndex
        Right other -> liftEffect $ throw ("one slot expected, got " <> show (Array.length other))
        Left e -> liftEffect $ throw (show e)
      liftEffect (Ref.read childInvocations) >>= (_ `shouldEqual` 0)
      liftEffect (Ref.read executions) >>= (_ `shouldEqual` 1)

      -- Iteration 3 reads the claimed output of iteration 2. Neither
      -- pending child invocation is requested when its debt is false.
      proveParent false second 3
      liftEffect (Ref.read childInvocations) >>= (_ `shouldEqual` 0)
      liftEffect (Ref.read executions) >>= (_ `shouldEqual` 2)

      -- Iteration 2 requires iteration 1. The parent runs once and the
      -- requested child runs once, with its own assignments.
      proveParent true first 2
      liftEffect (Ref.read childInvocations) >>= (_ `shouldEqual` 1)
      liftEffect (Ref.read executions) >>= (_ `shouldEqual` 4)

      -- Another parent shares the same reference and reuses its proof.
      proveParent true first 2
      liftEffect (Ref.read childInvocations) >>= (_ `shouldEqual` 1)
      liftEffect (Ref.read executions) >>= (_ `shouldEqual` 5)
