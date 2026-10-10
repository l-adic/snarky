-- | One compiled rule decides its proof obligation from private computation.
-- | Providers see returned statements, can recurse into the same prover, and
-- | are never forced for skipped slots. The rule witness runs once per call.
module Test.Pickles.Prove.DynamicProofDebt (spec) where

import Prelude

import Colog (LoggerT, Message, logInfo)
import Data.Array as Array
import Data.Either (Either(..))
import Data.Foldable (for_)
import Data.Maybe (Maybe(..))
import Data.String (contains)
import Data.String.Pattern (Pattern(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (Tuple1, Tuple2, tuple1, tuple2, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw)
import Effect.Ref (Ref)
import Effect.Ref as Ref
import Pickles (ApplicationStatement(..), BranchProver(..), CompiledProof(..), PrevSlot(..), PrevStatement(..), ProveError, Slot, SlotWrapKey(..), StepField, StepRule, Tag(..), compileMulti, mkRuleEntry, prevValues, toPrevs, toVerifiable, verify)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.CVar (EvaluationError(..), add_)
import Snarky.Circuit.DSL (F(..), FVar, assertEqual_, const_, equals_, exists)
import Test.Pickles.Outputs (appOutputs)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

type Statement = ApplicationStatement (F StepField) (F StepField)
type Prevs = Tuple1 (Slot 1 Statement)

-- | The private pair is (decision input, statement offset). Equality to one
-- | decides verification; the offset makes the returned statement differ
-- | from its initial advice. Neither computation is repeated by the caller.
dynamicRule
  :: Ref (Tuple (F StepField) (F StepField))
  -> Ref (Array String)
  -> StepRule Prevs (F StepField) (FVar StepField) (F StepField) (FVar StepField)
dynamicRule private events getPrevs _ = do
  Tuple decision offset <- exists $ liftEffect $ Ref.read private
  ApplicationStatement claimed <- exists $ getPrevs <#> prevValues <#> \(prev /\ _) -> prev
  mustVerify <- equals_ decision (const_ one)
  let
    returnedStatement = ApplicationStatement
      { input: add_ claimed.input offset
      , output: add_ claimed.output offset
      }
  _ :: Unit <- exists $ liftEffect $ Ref.modify_ (flip Array.snoc "rule") events
  pure
    { prevs: toPrevs $ PrevStatement { publicInput: returnedStatement, proofMustVerify: mustVerify } /\ unit
    , publicOutput: add_ claimed.output offset
    }

-- | Width-zero external input and width-two self output have different types.
type Counts = Tuple (F StepField) (F StepField)
type MixedPrevs =
  Tuple2
    (Slot 0 (ApplicationStatement (F StepField) Unit))
    (Slot 2 (ApplicationStatement Unit Counts))

childRule :: StepRule Unit (F StepField) (FVar StepField) Unit Unit
childRule _ _ = pure { prevs: toPrevs unit, publicOutput: unit }

baseRule :: StepRule Unit Unit Unit Counts (Tuple (FVar StepField) (FVar StepField))
baseRule _ _ = pure
  { prevs: toPrevs unit
  , publicOutput: Tuple (const_ zero) (const_ zero)
  }

mixedRule
  :: Ref (Tuple (F StepField) (F StepField))
  -> Ref (Array String)
  -> StepRule MixedPrevs Unit Unit Counts (Tuple (FVar StepField) (FVar StepField))
mixedRule private events getPrevs _ = do
  Tuple childDecision selfDecision <- exists $ liftEffect $ Ref.read private
  childInput <- exists $ getPrevs <#> prevValues <#> \(ApplicationStatement { input } /\ _) -> input
  Tuple count total <- exists $ getPrevs <#> prevValues <#> \(_ /\ ApplicationStatement { output } /\ _) -> output
  verifyChild <- equals_ childDecision (const_ one)
  verifySelf <- equals_ selfDecision (const_ one)
  _ :: Unit <- exists $ liftEffect $ Ref.modify_ (flip Array.snoc "rule") events
  pure
    { prevs: toPrevs $
        PrevStatement
          { publicInput: ApplicationStatement { input: childInput, output: unit }
          , proofMustVerify: verifyChild
          }
          /\ PrevStatement
            { publicInput: ApplicationStatement { input: unit, output: Tuple count total }
            , proofMustVerify: verifySelf
            }
          /\ unit
    , publicOutput: Tuple (add_ count (const_ one)) (add_ total childInput)
    }

statement :: F StepField -> F StepField -> Statement
statement input output = ApplicationStatement { input, output }

statementValues :: Statement -> Tuple (F StepField) (F StepField)
statementValues (ApplicationStatement s) = Tuple s.input s.output

expectRight :: forall a. Either ProveError a -> Effect a
expectRight = case _ of
  Left e -> throw (show e)
  Right p -> pure p

expectFailure :: forall a. String -> Either ProveError a -> Effect Unit
expectFailure expected = case _ of
  Right _ -> throw ("expected failure containing: " <> expected)
  Left e -> unless (contains (Pattern expected) (show e)) $ throw (show e)

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.DynamicProofDebt" do
  it "resolves private decisions once, preserves the witness through recursive proof generation, and rejects mismatches" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    outputs <- liftEffect $ appOutputs "DynamicProofDebt"
    private <- liftEffect $ Ref.new (Tuple (F zero) (F one))
    events <- liftEffect $ Ref.new []
    entry <- liftEffect $ mkRuleEntry @(F StepField) (dynamicRule private events) (Self :< Vector.nil)
    let
      config =
        { srs: { vestaSrs, pallasSrs }
        , debug: true
        , wrapDomainOverride: Nothing
        , proofCache: outputs.proofCache
        , lagrangeCache: Just lagrangeCache
        , dump: outputs.dumpAt "dynamic"
        }
    logInfo "[DynamicProofDebt] compiling…"
    app <- liftEffect $ compileMulti @(F StepField) @1 config (tuple1 entry)
    liftEffect (Ref.read events) >>= (_ `shouldEqual` [])
    let
      BranchProver prover = fst app.provers
      prove input prev = prover noAdvice { appInput: input, prevs: tuple1 prev }
      reset decision offset = do
        Ref.write (Tuple (F decision) (F offset)) private
        Ref.write [] events
      forbidden = DeferredPrev
        { statement: statement (F zero) (F zero)
        , obtainProof: \_ -> throw "a skipped proof provider was called"
        }
      check proof = verify app.verifier (toVerifiable proof) `shouldEqual` true

    -- False private decision still uses the witnessed statement in its output.
    base <- liftEffect $ prove (F one) forbidden >>= expectRight
    check base
    let CompiledProof baseRaw = base
    statementValues baseRaw.statement `shouldEqual` Tuple (F one) (F one)
    liftEffect (Ref.read events) >>= (_ `shouldEqual` [ "rule" ])

    -- The caller only supplies a proof source, not the circuit's decision.
    liftEffect $ reset one one
    let
      deferred = DeferredPrev
        { statement: statement (F zero) (F zero)
        , obtainProof: \actual -> do
            statementValues actual `shouldEqualEffect` Tuple (F one) (F one)
            Ref.modify_ (flip Array.snoc "provider") events
            pure $ Right { proof: base, tag: app.tag }
        }
    required <- liftEffect $ prove (F (one + one)) deferred >>= expectRight
    check required
    liftEffect (Ref.read events) >>= (_ `shouldEqual` [ "rule", "provider" ])

    -- A provider can reenter the same compiled prover. The parent retains
    -- the flag and assignments it computed before the child's private advice.
    liftEffect $ reset one one
    let
      nested = DeferredPrev
        { statement: statement (F zero) (F zero)
        , obtainProof: \(ApplicationStatement actual) -> do
            Ref.modify_ (flip Array.snoc "provider") events
            Ref.write (Tuple (F zero) (F one)) private
            child <- prove actual.input
              (BasePrev { dummyStatement: statement (actual.input - F one) (actual.output - F one) })
            Ref.write (Tuple (F one) (F one)) private
            pure $ child <#> \proof -> { proof, tag: app.tag }
        }
    recursive <- liftEffect $ prove (F (one + one)) nested >>= expectRight
    check recursive
    liftEffect (Ref.read events) >>= (_ `shouldEqual` [ "rule", "provider", "rule" ])

    -- Consume a proof that already carries debt, exercising both handovers
    -- when the exported cache is replayed through the application capstones.
    liftEffect $ reset one zero
    let
      descendantPrev = DeferredPrev
        { statement: statement (F (one + one)) (F one)
        , obtainProof: \actual -> do
            statementValues actual `shouldEqualEffect` Tuple (F (one + one)) (F one)
            Ref.modify_ (flip Array.snoc "provider") events
            pure $ Right { proof: required, tag: app.tag }
        }
    descendant <- liftEffect $ prove (F (one + one + one)) descendantPrev >>= expectRight
    check descendant
    liftEffect (Ref.read events) >>= (_ `shouldEqual` [ "rule", "provider" ])

    -- The same prover must not retain prepared state or an earlier flag.
    liftEffect $ reset zero one
    skippedAgain <- liftEffect $ prove (F one) forbidden >>= expectRight
    check skippedAgain
    liftEffect (Ref.read events) >>= (_ `shouldEqual` [ "rule" ])

    -- Legacy availability is independent of verification. Its statement may
    -- be transformed when the proof is unused, and still determines output.
    liftEffect $ reset zero one
    unusedReal <- liftEffect $ prove (F one) (InductivePrev base app.tag) >>= expectRight
    check unusedReal
    let CompiledProof unusedRaw = unusedReal
    statementValues unusedRaw.statement `shouldEqual` Tuple (F one) (F (one + one))
    liftEffect $ reset one zero
    usedReal <- liftEffect $ prove (F one) (InductivePrev base app.tag) >>= expectRight
    check usedReal

    -- A required BasePrev and explicit provider failure both abort resolution.
    liftEffect $
      prove (F one)
        (BasePrev { dummyStatement: statement (F one) (F one) })
        >>= expectFailure "required proof is missing"
    liftEffect $
      prove (F one)
        ( DeferredPrev
            { statement: statement (F one) (F one)
            , obtainProof: \_ -> pure $ Left (FailedAssertion "provider refused")
            }
        )
        >>= expectFailure "provider refused"

    -- Reuse succeeds after failure. A different statement must reach a fresh
    -- provider; the earlier proof cannot silently satisfy this obligation.
    liftEffect $ reset one one
    let
      wrongStatement = DeferredPrev
        { statement: statement (F one) (F one)
        , obtainProof: \actual -> do
            statementValues actual `shouldEqualEffect` Tuple (F (one + one)) (F (one + one))
            pure $ Right { proof: base, tag: app.tag }
        }
    liftEffect $ prove (F one) wrongStatement >>= expectFailure "proof statement does not match"
    liftEffect $ reset one zero
    afterFailure <- liftEffect $ prove (F one) (InductivePrev base app.tag) >>= expectRight
    check afterFailure

    -- Source metadata cannot override the slot's compiled configuration.
    let
      badChunks = case app.tag of
        Tag tag -> Tag (tag { verifier = tag.verifier { stepZkRows = tag.verifier.stepZkRows + 1 } })
      badDomain = CompiledProof (baseRaw { stepDomainLog2 = 30 })
    liftEffect $ prove (F one) (InductivePrev base badChunks)
      >>= expectFailure "proof step chunk count does not match"
    liftEffect $ prove (F one) (InductivePrev badDomain app.tag)
      >>= expectFailure "proof step domain is not a branch"

    -- A second application has the same statement type/width but a different
    -- constraint and key. Its matching statement does not make it this source.
    let
      otherRule :: StepRule Prevs (F StepField) (FVar StepField) (F StepField) (FVar StepField)
      otherRule getPrevs input = do
        result <- dynamicRule private events getPrevs input
        assertEqual_ input (const_ zero)
        pure result
    otherEntry <- liftEffect $ mkRuleEntry @(F StepField) otherRule (Self :< Vector.nil)
    other <- liftEffect $ compileMulti @(F StepField) @1
      (config { dump = Nothing, proofCache = Nothing })
      (tuple1 otherEntry)
    let BranchProver otherProver = fst other.provers
    liftEffect $ reset zero one
    wrongSource <- liftEffect $
      otherProver noAdvice
        { appInput: F zero, prevs: tuple1 (BasePrev { dummyStatement: statement (F zero) (F zero) }) }
        >>= expectRight
    liftEffect $ reset one zero
    liftEffect $ prove (F one) (InductivePrev wrongSource other.tag)
      >>= expectFailure "proof verification key does not match"

    -- Spoofing the carried statement passes the cheap field comparison, but
    -- the cryptographic checks still bind the proof to its original statement.
    liftEffect $ reset one one
    let
      forged = CompiledProof (baseRaw { statement = statement (F (one + one)) (F (one + one)) })
      spoofed = DeferredPrev
        { statement: statement (F one) (F one)
        , obtainProof: \_ -> pure $ Right { proof: forged, tag: app.tag }
        }
    liftEffect $ prove (F one) spoofed >>= expectFailure "FailedAssertion"

    -- Private values other than one also produce the false circuit decision.
    liftEffect $ reset (one + one) one
    final <- liftEffect $ prove (F one) forbidden >>= expectRight
    check final
    liftEffect (Ref.read events) >>= (_ `shouldEqual` [ "rule" ])
    logInfo "[DynamicProofDebt] dynamic, nested, and failure checks passed"

  it "handles all private verification masks with heterogeneous slots and a padded producing branch" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    outputs <- liftEffect $ appOutputs "DynamicProofDebt"
    private <- liftEffect $ Ref.new (Tuple (F zero) (F zero))
    events <- liftEffect $ Ref.new []
    let
      config =
        { srs: { vestaSrs, pallasSrs }
        , debug: true
        , wrapDomainOverride: Nothing
        , proofCache: outputs.proofCache
        , lagrangeCache: Just lagrangeCache
        , dump: outputs.dumpAt "child"
        }
    childEntry <- liftEffect $ mkRuleEntry @Unit childRule Vector.nil
    child <- liftEffect $ compileMulti @Unit @1 config (tuple1 childEntry)
    let BranchProver childProver = fst child.provers
    childProof <- liftEffect $ childProver noAdvice { appInput: F one, prevs: unit } >>= expectRight
    baseEntry <- liftEffect $ mkRuleEntry @Counts baseRule Vector.nil
    mixedEntry <- liftEffect $ mkRuleEntry @Counts (mixedRule private events)
      (External child.tagData :< Self :< Vector.nil)
    app <- liftEffect $ compileMulti @Counts @1
      (config { wrapDomainOverride = Just 14, dump = outputs.dumpAt "mixed" })
      (tuple2 baseEntry mixedEntry)
    liftEffect (Ref.read events) >>= (_ `shouldEqual` [])
    let
      BranchProver baseProver = fst app.provers
      BranchProver mixedProver = fst (snd app.provers)
    base <- liftEffect $ baseProver noAdvice { appInput: unit, prevs: unit } >>= expectRight
    verify app.verifier (toVerifiable base) `shouldEqual` true
    let
      childPrev = DeferredPrev
        { statement: ApplicationStatement { input: F one, output: unit }
        , obtainProof: \(ApplicationStatement actual) -> do
            actual.input `shouldEqualEffect` F one
            Ref.modify_ (flip Array.snoc "child") events
            pure $ Right { proof: childProof, tag: child.tag }
        }
      selfPrev = DeferredPrev
        { statement: ApplicationStatement { input: unit, output: Tuple (F zero) (F zero) }
        , obtainProof: \(ApplicationStatement actual) -> do
            actual.output `shouldEqualEffect` Tuple (F zero) (F zero)
            Ref.modify_ (flip Array.snoc "self") events
            pure $ Right { proof: base, tag: app.tag }
        }
    for_ [ Tuple false false, Tuple false true, Tuple true false, Tuple true true ] \(Tuple childRequired selfRequired) -> do
      liftEffect do
        Ref.write (Tuple (F (if childRequired then one else zero)) (F (if selfRequired then one else zero))) private
        Ref.write [] events
      proof <- liftEffect $
        mixedProver noAdvice
          { appInput: unit, prevs: tuple2 childPrev selfPrev } >>= expectRight
      verify app.verifier (toVerifiable proof) `shouldEqual` true
      let CompiledProof raw = proof
      case raw.statement of
        ApplicationStatement actual -> actual.output `shouldEqual` Tuple (F one) (F one)
      liftEffect (Ref.read events) >>=
        ( _ `shouldEqual`
            ([ "rule" ] <> (if childRequired then [ "child" ] else []) <> (if selfRequired then [ "self" ] else []))
        )
    logInfo "[DynamicProofDebt] heterogeneous masks and padding checks passed"

-- | Assertions inside the synchronous provider remain in Effect.
shouldEqualEffect :: forall a. Eq a => Show a => a -> a -> Effect Unit
shouldEqualEffect actual expected = unless (actual == expected)
  $ throw ("expected " <> show expected <> ", got " <> show actual)
