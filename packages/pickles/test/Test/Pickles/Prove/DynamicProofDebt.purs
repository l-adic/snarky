-- | One incrementer, compiled once, takes its proof-debt flag directly from
-- | Boolean advice. The Int test driver requires the previous proof on even
-- | iterations; the circuit does not define parity over field elements.
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
import Pickles (ApplicationStatement(..), BranchProver(..), CompiledProof(..), PrevSlot(..), PrevStatement(..), ProveError, Slot, SlotWrapKey(..), StepField, StepRule, Tag(..), Verifier, compileMulti, mkRuleEntry, prevValues, provedPrev, toPrevs, toVerifiable, unprovedPrev, verify)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.CVar (EvaluationError(..), add_)
import Snarky.Circuit.DSL (F(..), FVar, const_, exists)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.Outputs (appOutputs)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, aroundWith, beforeAll, beforeWith, describe, it, sequential)
import Test.Spec.Assertions (shouldEqual)

type Statement = ApplicationStatement Unit (F StepField)
type Proof = CompiledProof 1 Statement
type Prevs = Tuple1 (Slot 1 Statement)
type TestM = LoggerT Message Aff

type Fixture =
  { prove :: PrevSlot Unit 1 Statement -> Effect (Either ProveError Proof)
  , tag :: Tag Statement 1
  , verifier :: Verifier
  , seed :: Proof
  , mustVerify :: Ref Boolean
  , events :: Ref (Array String)
  }

incrementRule
  :: Ref Boolean
  -> Ref (Array String)
  -> StepRule Prevs Unit Unit (F StepField) (FVar StepField)
incrementRule advice events getPrevs _ = do
  previous <- exists $ getPrevs <#> prevValues <#> \(s /\ _) -> s
  mustVerify <- exists $ liftEffect $ Ref.read advice
  _ :: Unit <- exists $ liftEffect $ Ref.modify_ (flip Array.snoc "rule") events
  let ApplicationStatement { output: counter } = previous
  pure
    { prevs: toPrevs $ PrevStatement { publicInput: previous, proofMustVerify: mustVerify } /\ unit
    , publicOutput: add_ counter (const_ one)
    }

statement :: Int -> Statement
statement counter = ApplicationStatement { input: unit, output: F (fromInt counter) }

buildFixture :: SharedSrs -> TestM Fixture
buildFixture { pallasSrs, vestaSrs, lagrangeCache } = do
  outputs <- liftEffect $ appOutputs "DynamicProofDebt"
  mustVerify <- liftEffect $ Ref.new false
  events <- liftEffect $ Ref.new []
  entry <- liftEffect $ mkRuleEntry @(F StepField) (incrementRule mustVerify events) (Self :< Vector.nil)
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
  liftEffect (Ref.read events) >>= (_ `shouldEqual` [])
  let
    BranchProver prover = fst app.provers
    prove prev = prover noAdvice { appInput: unit, prevs: tuple1 prev }
  seed <- liftEffect $ prove (unprovedPrev (statement 0)) >>= expectRight
  pure { prove, tag: app.tag, verifier: app.verifier, seed, mustVerify, events }

-- | This spec version's beforeAll does not accept an inherited input. The
-- | outer hook supplies the existing SharedSrs to its one-time setup action.
withFixture :: SpecT TestM Fixture Aff Unit -> SpecT TestM SharedSrs Aff Unit
withFixture tests = do
  setup <- liftEffect $ Ref.new (liftEffect $ throw "incrementer setup needs SharedSrs")
  aroundWith (\run srs -> liftEffect (Ref.write (buildFixture srs) setup) *> run unit)
    $ beforeAll (join $ liftEffect $ Ref.read setup)
    $
      beforeWith
        ( \fixture -> do
            liftEffect do
              Ref.write false fixture.mustVerify
              Ref.write [] fixture.events
            pure fixture
        )
        (sequential tests)

spec :: SpecT TestM SharedSrs Aff Unit
spec = withFixture $ describe "Pickles.Prove.DynamicProofDebt" do
  it "increments from zero and requires the previous proof only on even iterations" \fixture -> do
    _ <- foldM
      ( \previous iteration -> do
          let required = iteration `mod` 2 == 0
          liftEffect do
            Ref.write required fixture.mustVerify
            Ref.write [] fixture.events
          let
            prev = DeferredPrev
              { statement: statement (iteration - 1)
              , obtainProof: \actual -> do
                  assertStatement (iteration - 1) actual
                  Ref.modify_ (flip Array.snoc "provider") fixture.events
                  case previous of
                    Nothing -> throw "proof requested before the first increment"
                    Just proof -> pure $ Right { proof, tag: fixture.tag }
              }
          proof <- liftEffect $ fixture.prove prev >>= expectRight
          checkProof fixture iteration proof
          liftEffect (Ref.read fixture.events) >>=
            (_ `shouldEqual` ([ "rule" ] <> if required then [ "provider" ] else []))
          pure (Just proof)
      )
      Nothing
      [ 1, 2, 3, 4 ]
    pure unit

  it "uses an unproved counter while never calling its skipped provider" \fixture -> do
    proof <- liftEffect $
      fixture.prove
        ( DeferredPrev
            { statement: statement 2
            , obtainProof: \_ -> throw "a skipped proof provider was called"
            }
        ) >>= expectRight
    checkProof fixture 3 proof
    liftEffect (Ref.read fixture.events) >>= (_ `shouldEqual` [ "rule" ])

  it "reports unavailable proofs and provider failures, then allows the next call to succeed" \fixture -> do
    liftEffect $ Ref.write true fixture.mustVerify
    missing <- liftEffect $ fixture.prove (unprovedPrev (statement 1))
    liftEffect do
      expectFailure "required proof is missing" missing
      expectFailure "branch 0 slot 0" missing
    liftEffect $
      fixture.prove
        ( DeferredPrev
            { statement: statement 1
            , obtainProof: \_ -> pure $ Left (FailedAssertion "provider refused")
            }
        ) >>= expectFailure "provider refused"
    proof <- liftEffect $ fixture.prove (provedPrev fixture.seed fixture.tag) >>= expectRight
    checkProof fixture 2 proof

  it "retains the consuming rule's witness when its provider invokes the same prover" \fixture -> do
    liftEffect $ Ref.write true fixture.mustVerify
    let
      prev = DeferredPrev
        { statement: statement 1
        , obtainProof: \actual -> do
            assertStatement 1 actual
            Ref.modify_ (flip Array.snoc "provider") fixture.events
            Ref.write false fixture.mustVerify
            child <- fixture.prove (unprovedPrev (statement 0))
            pure $ child <#> \proof -> { proof, tag: fixture.tag }
        }
    proof <- liftEffect $ fixture.prove prev >>= expectRight
    checkProof fixture 2 proof
    liftEffect (Ref.read fixture.events) >>= (_ `shouldEqual` [ "rule", "provider", "rule" ])
    liftEffect (Ref.read fixture.mustVerify) >>= (_ `shouldEqual` false)
    liftEffect $ Ref.write [] fixture.events
    skipped <- liftEffect $ fixture.prove (unprovedPrev (statement 2)) >>= expectRight
    checkProof fixture 3 skipped
    liftEffect (Ref.read fixture.events) >>= (_ `shouldEqual` [ "rule" ])

  it "rejects proofs with a different statement or incompatible source metadata" \fixture -> do
    liftEffect $ Ref.write true fixture.mustVerify
    liftEffect $
      fixture.prove
        ( DeferredPrev
            { statement: statement 2
            , obtainProof: \_ -> pure $ Right { proof: fixture.seed, tag: fixture.tag }
            }
        ) >>= expectFailure "proof statement does not match"
    let
      badChunks = case fixture.tag of
        Tag tag -> Tag (tag { verifier = tag.verifier { stepZkRows = tag.verifier.stepZkRows + 1 } })
      CompiledProof raw = fixture.seed
      badDomain = CompiledProof (raw { stepDomainLog2 = 30 })
    liftEffect $ fixture.prove (provedPrev fixture.seed badChunks)
      >>= expectFailure "proof step chunk count does not match"
    liftEffect $ fixture.prove (provedPrev badDomain fixture.tag)
      >>= expectFailure "proof step domain is not a branch"

  it "rejects forged statement metadata even when it matches the requested counter" \fixture -> do
    liftEffect $ Ref.write true fixture.mustVerify
    let
      CompiledProof raw = fixture.seed
      forged = CompiledProof (raw { statement = statement 2 })
    liftEffect $ fixture.prove (provedPrev forged fixture.tag)
      >>= expectFailure "FailedAssertion"

checkProof :: Fixture -> Int -> Proof -> TestM Unit
checkProof fixture counter proof@(CompiledProof raw) = do
  liftEffect $ assertStatement counter raw.statement
  verify fixture.verifier (toVerifiable proof) `shouldEqual` true

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
