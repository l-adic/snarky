-- | A side-loaded slot whose rule binds its key with `bindVk`: the
-- | parent's public input is the key's `digest_vk`. The child is
-- | `SideLoadedMain`'s. Proving at the child key's digest succeeds and
-- | verifies; proving the same child, key and proof at any other digest
-- | yields no proof.
module Test.Pickles.Prove.SideLoadedBound
  ( spec
  ) where

import Prelude

import Colog (LoggerT, Message, withSpan)
import Data.Either (Either(..))
import Data.Maybe (Maybe(..))
import Data.Tuple (fst)
import Data.Tuple.Nested (tuple1, (/\))
import Data.Vector as Vector
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Effect.Exception (try)
import Pickles (ApplicationStatement(..), CompiledProof, ProofsVerified(..), SideLoadedPrev(..), SideLoadedPrevStatement(..), StepField, StepRule, WrapVkChunks, bindVk, compileMulti, mkRuleEntry, prevValues, proveBranch, provedPrev, toPrevs, toVerifiable, verify)
import Pickles.Sideload (digestVk, mkBundle, projectVk) as Sideload
import Safe.Coerce (coerce)
import Snarky.Backend.Advice (noAdvice)
import Snarky.Circuit.DSL (F(..), FVar, exists, true_)
import Test.Pickles.Outputs (appOutputs)
import Test.Pickles.Prove.SideLoadedMain (SideLoadedMainPrevsSpec, noRecursionInputRule)
import Test.Pickles.SharedSrs (SharedSrs)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (fail, shouldEqual)

-- | The parent rule: its side-loaded slot verifies the child against a
-- | key whose digest is `self`.
sideLoadedBoundRule
  :: StepRule SideLoadedMainPrevsSpec
       (F StepField)
       (FVar StepField)
       Unit
       Unit
sideLoadedBoundRule getPrevStates self = do
  prev <- exists $ getPrevStates <#> prevValues <#> \(slot /\ _) ->
    let ApplicationStatement { input } = slot.statement in input
  vk <- exists $ getPrevStates <#> prevValues <#> \(slot /\ _) -> slot.verificationKey
  boundVk <- bindVk self vk
  pure
    { prevs: toPrevs $
        SideLoadedPrevStatement
          { publicInput: ApplicationStatement { input: prev, output: unit }
          , proofMustVerify: true_
          , verificationKey: boundVk
          }
          /\ unit
    , publicOutput: unit
    }

spec :: SpecT (LoggerT Message Aff) SharedSrs Aff Unit
spec = describe "Pickles.Prove.SideLoadedBound" do
  it "proves at the side-loaded key's digest and fails at any other" \{ pallasSrs, vestaSrs, lagrangeCache } -> do
    outputs <- liftEffect $ appOutputs "SideLoadedBound"
    let
      compileCfg =
        { srs: { vestaSrs, pallasSrs }
        , debug: false
        , wrapDomainOverride: Nothing
        , proofCache: outputs.proofCache
        , lagrangeCache: Just lagrangeCache
        , dump: Nothing
        }

    childEntry <- liftEffect $ mkRuleEntry @Unit noRecursionInputRule Vector.nil
    child <- withSpan "[SideLoadedBound] compile child" $ liftEffect $ compileMulti @Unit @1 compileCfg
      (tuple1 childEntry)
    let childProver = proveBranch (fst child.provers)
    eChildCp <- withSpan "[SideLoadedBound] prove child" $ liftEffect $ childProver noAdvice
      { appInput: F zero, prevs: unit }
    childCp0 :: CompiledProof 0 (ApplicationStatement (F StepField) Unit) <- case eChildCp of
      Left e -> liftEffect $ Exc.throw ("childProver: " <> show e)
      Right cp -> pure cp

    -- The proof's width is phantom, as in `SideLoadedMain`.
    let
      childCp2 :: CompiledProof 2 (ApplicationStatement (F StepField) Unit)
      childCp2 = coerce childCp0

      childVK = Sideload.mkBundle @WrapVkChunks
        { verifierIndex: child.vks.wrap.verifierIndex
        , maxProofsVerified: N0
        , actualWrapDomainSize: N0
        }

      digest = Sideload.digestVk (Sideload.projectVk childVK)

      prevs = tuple1 (SideLoadedPrev childVK (provedPrev childCp2))

    parentEntry <- liftEffect $ mkRuleEntry @Unit sideLoadedBoundRule Vector.nil
    parent <- withSpan "[SideLoadedBound] compile parent" $ liftEffect $ compileMulti @Unit @1 compileCfg
      (tuple1 parentEntry)
    let parentProver = proveBranch (fst parent.provers)

    eBound <- withSpan "[SideLoadedBound] prove at the key's digest" $ liftEffect $ parentProver noAdvice
      { appInput: F digest, prevs }
    boundCp <- case eBound of
      Left e -> liftEffect $ Exc.throw ("parentProver at the key's digest: " <> show e)
      Right cp -> pure cp
    verify parent.verifier (toVerifiable boundCp) `shouldEqual` true

    -- The same child, key and proof at another digest. `self` is read
    -- only by `bindVk`, so the witness breaks just the binding's
    -- equality. Outside debug mode the solver does not check
    -- constraints, and kimchi rejects the witness.
    eOther <- withSpan "[SideLoadedBound] prove at another digest" $ liftEffect $ try $ parentProver noAdvice
      { appInput: F (digest + one), prevs }
    case eOther of
      Right (Right _) -> fail "proved at a digest that is not the key's"
      _ -> pure unit
