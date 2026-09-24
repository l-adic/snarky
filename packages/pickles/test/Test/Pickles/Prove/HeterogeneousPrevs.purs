-- | Slots and branches whose previous statements have different types.
-- |
-- | A separately compiled input-mode `childRule` has statement
-- | `StatementIO (F StepField) Unit`, one field. The application under
-- | test has statement `StatementIO Unit (Tuple (F StepField) (F StepField))`,
-- | two fields, and two branches with different prev shapes: `baseRule`
-- | has no slots, and `absorbRule` has an `External` slot at the child's
-- | statement and a `Self` slot at its own.
-- |
-- | Each `absorbRule` step counts itself and adds the child's input to
-- | a running sum. The chain b0..b2 must produce `(0, 0)`, `(1, 7)` and
-- | `(2, 14)` and verify in one batch, so it fails if a slot's statement
-- | is encoded at another slot's type or width.
module Test.Pickles.Prove.HeterogeneousPrevs
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (Tuple(..), fst, snd)
import Data.Tuple.Nested (Tuple2, tuple1, tuple2, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), CompiledProof(..), PrevSlot(..), PrevStatement(..), RulesCons, RulesNil, Slot, SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, prevValues, toPrevs, toVerifiable, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, const_, exists, true_)
import Snarky.Curves.Class (fromInt)
import Test.Pickles.SerializeRoundTrip (mkWidthDummies, roundTripAndVerify)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The application's statement output: a step count and a running sum.
type Counts = Tuple (F StepField) (F StepField)

--------------------------------------------------------------------------------
-- The child
--------------------------------------------------------------------------------

-- | An input-mode rule with no prevs; its public input is unconstrained.
childRule :: StepRule Unit (F StepField) (FVar StepField) Unit Unit
childRule _ _ = pure
  { prevs: toPrevs unit
  , publicOutput: unit
  }

type ChildRules = RulesCons 0 Unit RulesNil

--------------------------------------------------------------------------------
-- The application
--------------------------------------------------------------------------------

-- | Branch 0: no prevs, output `(0, 0)`.
baseRule :: StepRule Unit Unit Unit Counts (Tuple (FVar StepField) (FVar StepField))
baseRule _ _ = pure
  { prevs: toPrevs unit
  , publicOutput: Tuple (const_ zero) (const_ zero)
  }

-- | Branch 1's slots: the child's one-field input statement at width 0,
-- | then this application's two-field output statement at width 2.
type AbsorbPrevsSpec =
  Tuple2
    (Slot 0 (StatementIO (F StepField) Unit))
    (Slot 2 (StatementIO Unit Counts))

-- | Branch 1: output the self prev's count plus one, and its sum plus
-- | the child's input. Both prevs always verify; the chain's base case
-- | is a branch-0 proof.
absorbRule
  :: StepRule AbsorbPrevsSpec Unit Unit Counts (Tuple (FVar StepField) (FVar StepField))
absorbRule getPrevStates _ = do
  childInput <- exists $ getPrevStates <#> prevValues <#> \(StatementIO { input } /\ _) -> input
  Tuple prevCount prevSum <- exists $ getPrevStates <#> prevValues <#>
    \(_ /\ StatementIO { output } /\ _) -> output
  pure
    { prevs: toPrevs $
        PrevStatement { publicInput: StatementIO { input: childInput, output: unit }, proofMustVerify: true_ }
          /\ PrevStatement { publicInput: StatementIO { input: unit, output: Tuple prevCount prevSum }, proofMustVerify: true_ }
          /\ unit
    , publicOutput: Tuple (CVar.add_ (const_ one) prevCount) (CVar.add_ prevSum childInput)
    }

type AppRules =
  RulesCons 0 Unit
    ( RulesCons 2
        AbsorbPrevsSpec
        RulesNil
    )

--------------------------------------------------------------------------------
-- Test spec
--------------------------------------------------------------------------------

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.HeterogeneousPrevs" do
  it "b0..b2 across two branches whose slots carry 1- and 2-field statements" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/HeterogeneousPrevs.json")

    let dummies = mkWidthDummies pallasSrs vestaSrs

    childEntry <- liftEffect $ mkRuleEntry @0 @Unit childRule Vector.nil
    logInfo "[HeterogeneousPrevs] compiling child…"
    child <- withSpan "[HeterogeneousPrevs] compile child" $ liftEffect $ compileMulti
      @ChildRules
      @Unit
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      (tuple1 childEntry)

    let BranchProver childProver = fst child.provers
    eChild <- withSpan "[HeterogeneousPrevs] prove child" $ liftEffect $ childProver noAdvice
      { appInput: F (fromInt 7), prevs: unit }
    childCp <- case eChild of
      Left e -> liftEffect $ Exc.throw ("childProver: " <> show e)
      Right p -> pure p
    childCp' <- roundTripAndVerify dummies child.verifier childCp

    let
      childProverVKs =
        { stepCompileResult: fst child.vks.perBranchStep
        , wrapCompileResult: child.vks.wrap
        , wrapDomainLog2: child.vks.wrapDomainLog2
        , stepNumChunks: child.vks.stepChunks
        }

    baseEntry <- liftEffect $ mkRuleEntry @2 @Counts baseRule Vector.nil
    absorbEntry <- liftEffect $ mkRuleEntry @2 @Counts absorbRule
      (External childProverVKs :< Self :< Vector.nil)

    logInfo "[HeterogeneousPrevs] compiling application…"
    -- The slot widths 0 and 2 give a smaller wrap circuit than the
    -- default domain for `mpvMax = 2` assumes.
    app <- withSpan "[HeterogeneousPrevs] compile application" $ liftEffect $ compileMulti
      @AppRules
      @Counts
      @1
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Just 14
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      (tuple2 baseEntry absorbEntry)

    let
      BranchProver baseProver = fst app.provers
      BranchProver absorbProver = fst (snd app.provers)

      runAbsorb
        :: PrevSlot Unit 2 (StatementIO Unit Counts)
        -> Aff (CompiledProof 2 (StatementIO Unit Counts))
      runAbsorb selfPrev = do
        eRes <- liftEffect $ absorbProver noAdvice
          { appInput: unit
          , prevs: tuple2 (InductivePrev childCp' child.tag) selfPrev
          }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("absorbProver: " <> show e)
          Right p -> pure p

    logInfo "[HeterogeneousPrevs] proving b0 (base branch)"
    eB0 <- withSpan "[HeterogeneousPrevs] prove b0" $ liftEffect $ baseProver noAdvice
      { appInput: unit, prevs: unit }
    b0 <- case eB0 of
      Left e -> liftEffect $ Exc.throw ("baseProver: " <> show e)
      Right p -> pure p
    b0' <- roundTripAndVerify dummies app.verifier b0

    logInfo "[HeterogeneousPrevs] proving b1 (absorb over b0)"
    b1 <- withSpan "[HeterogeneousPrevs] prove b1" $ liftAff $ runAbsorb (InductivePrev b0' app.tag)
    b1' <- roundTripAndVerify dummies app.verifier b1

    logInfo "[HeterogeneousPrevs] proving b2 (absorb over b1)"
    b2 <- withSpan "[HeterogeneousPrevs] prove b2" $ liftAff $ runAbsorb (InductivePrev b1' app.tag)

    verifyBatch app.verifier (map toVerifiable [ b0, b1, b2 ]) `shouldEqual` true

    let outputOf (CompiledProof p) = let StatementIO s = p.statement in s.output
    map outputOf [ b0, b1, b2 ] `shouldEqual`
      [ Tuple (F zero) (F zero)
      , Tuple (F one) (F (fromInt 7))
      , Tuple (F (fromInt 2)) (F (fromInt 14))
      ]
