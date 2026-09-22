-- | The self-recursive chain at two chunks: `simpleChainRule`'s
-- | `self == prev + 1` with a body that fills 2^16 rows, declared at
-- | `stepChunks = 2`, proved at the base case and at one inductive
-- | step.
-- |
-- | The base case's dummy prev carries its evaluations at two chunks,
-- | padded with zeros, and b1 verifies b0. So this is the first proof
-- | of a chunked self-recursive chain, and the step after it.
module Test.Pickles.Prove.SelfRecursiveChunks
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, logInfo, withSpan)
import Control.Monad.Rec.Class (Step(..), tailRecM)
import Data.Either (Either(..))
import Data.Int.Bits as Bits
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (Tuple1, tuple1, (/\))
import Data.Vector ((:<))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Aff.Class (liftAff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Node.Process (lookupEnv)
import Pickles (BranchProver(..), CompiledProof(..), PrevSlot(..), PrevStatement(..), RulesCons, RulesNil, Slot, SlotProveVk(..), SlotWrapKey(..), StatementIO(..), StepField, StepRule, compileMulti, mkRuleEntry, prevValues, toPrevs, toVerifiable, verifyBatch)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Backend.Kimchi.ProofCache (mkProofCache)
import Snarky.Circuit.CVar (add_) as CVar
import Snarky.Circuit.DSL (F(..), FVar, addConstraint, assertAny_, const_, equals_, exists, mul_, not_)
import Snarky.Circuit.Types (NoOutput(..))
import Snarky.Constraint.Kimchi (KimchiConstraint(..))
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | `self == prev + 1`, or `self == 0` at the base case, then 2^17 + 1
-- | `mul_` fillers on fresh zeros and one 7-wire Raw Generic, which
-- | pushes the 7th permuted column's degree past 2^16.
selfRecursiveChunksRule
  :: StepRule SelfRecursiveChunksPrevsSpec
       (F StepField)
       (FVar StepField)
       NoOutput
       NoOutput
selfRecursiveChunksRule getPrevStates self = do
  prev <- exists $ getPrevStates <#> prevValues <#> \(StatementIO { input } /\ _) -> input
  isBaseCase <- equals_ (const_ zero) self
  let proofMustVerify = not_ isBaseCase
  selfCorrect <- equals_ (CVar.add_ (const_ one) prev) self
  assertAny_ [ selfCorrect, isBaseCase ]
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
    { prevs: toPrevs $
        PrevStatement { publicInput: StatementIO { input: prev, output: NoOutput }, proofMustVerify }
          /\ unit
    , publicOutput: NoOutput
    }

-- | The rule's one self-recursive prev slot, at width 1.
type SelfRecursiveChunksPrevsSpec =
  Tuple1 (Slot 1 (StatementIO (F StepField) NoOutput))

-- | Carrier for the single rule.
type SelfRecursiveChunksRules =
  RulesCons 1
    SelfRecursiveChunksPrevsSpec
    RulesNil

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.SelfRecursiveChunks" do
  it "a chunks=2 self-recursive chain proves its base case and one step" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    cache <- liftEffect $ lookupEnv "PICKLES_PROOF_CACHE_DIR" <#> map \dir -> mkProofCache (dir <> "/SelfRecursiveChunks.json")

    entry <- liftEffect $ mkRuleEntry @1 @NoOutput selfRecursiveChunksRule (Self :< Vector.nil)

    logInfo "[SelfRecursiveChunks] compiling…"
    output <- withSpan "[SelfRecursiveChunks] compile" $ liftEffect $ compileMulti
      @SelfRecursiveChunksRules
      @NoOutput
      @2
      noAdvice
      { srs: { vestaSrs, pallasSrs }
      , debug: false
      , wrapDomainOverride: Nothing
      , proofCache: cache
      , lagrangeCache: Just lagrangeCache
      }
      (tuple1 entry)

    let
      BranchProver prover = fst output.provers

      runStep
        :: PrevSlot (F StepField) 1 (StatementIO (F StepField) NoOutput)
        -> F StepField
        -> Aff (CompiledProof 1 (StatementIO (F StepField) NoOutput))
      runStep prevSlot appInput = do
        eRes <- liftEffect $ prover noAdvice
          { appInput, prevs: tuple1 prevSlot, sideloadedVKs: tuple1 NoSideLoadedVk }
        case eRes of
          Left e -> liftEffect $ Exc.throw ("prover: " <> show e)
          Right p -> pure p

      basePrev = BasePrev
        { dummyStatement: StatementIO { input: F (negate one), output: NoOutput } }

    logInfo "[SelfRecursiveChunks] proving [step0, wrap0]"
    b0 <- withSpan "[SelfRecursiveChunks] prove b0" $ liftAff $ runStep basePrev (F zero)
    logInfo "[SelfRecursiveChunks] proving [step1, wrap1]"
    b1 <- withSpan "[SelfRecursiveChunks] prove b1" $ liftAff $ runStep (InductivePrev b0 output.tag) (F one)

    verifyBatch output.verifier (map toVerifiable [ b0, b1 ]) `shouldEqual` true
    let
      stmtInputOf (CompiledProof p) =
        let StatementIO s = p.statement in s.input
    map stmtInputOf [ b0, b1 ] `shouldEqual` [ F zero, F one ]
