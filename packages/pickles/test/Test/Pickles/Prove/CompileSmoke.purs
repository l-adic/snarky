-- | Smoke test for `Pickles.Prove.Compile.compile` on the NRR shape.
-- |
-- | Compiles the NRR rule via the new `compile` API, runs
-- | `prover.step`, and asserts both that `verifier.verify` accepts the
-- | resulting proof and that the wrap public-input bytes match what
-- | `produceNoRecursionReturn` generates for the same inputs. Kimchi's
-- | deterministic RNG (seed 42) guarantees the two paths produce
-- | identical proofs.
module Test.Pickles.Prove.CompileSmoke
  ( spec
  ) where

import Prelude

import Control.Monad.Except (runExceptT)
import Data.Either (Either(..))
import Data.Int.Bits as Int
import Data.Tuple (Tuple(..))
import Data.Vector as Vector
import Effect (Effect)
import Effect.Aff (Aff)
import Effect.Class (liftEffect)
import Effect.Exception (throw) as Exc
import Data.Newtype (un)
import Pickles.Prove.Compile (CompiledProof(..), PrevSlot(..), Tag(..), compile, verify, wrapPublicInput)
import Pickles.Prove.Step (StepRule)
import Pickles.Step.Prevs (PrevsSpecCons, PrevsSpecNil)
import Pickles.Types (StatementIO, StepField)
import Snarky.Backend.Kimchi.Class (createCRS)
import Snarky.Backend.Kimchi.Impl.Pallas as PallasImpl
import Snarky.Circuit.DSL (F(..), FVar, const_)
import Test.Pickles.Prove.NoRecursionReturn.Producer (produceNoRecursionReturn)
import Test.Pickles.Prove.SimpleChain (simpleChainRule)
import Test.Spec (SpecT, describe, it)
import Test.Spec.Assertions (shouldEqual)

-- | The NRR inductive rule — Output mode, N=0, returns `F zero`.
-- | Same rule body as `Test.Pickles.Prove.NoRecursionReturn.Producer.nrrRule`,
-- | re-declared here to exercise the compile API without dragging the
-- | producer's private definition.
nrrRule :: StepRule 0 Unit Unit (F StepField) (FVar StepField) Unit Unit
nrrRule _ = pure
  { prevPublicInputs: Vector.nil
  , proofMustVerify: Vector.nil
  , publicOutput: const_ zero
  }

spec :: SpecT Aff Unit Aff Unit
spec = describe "Pickles.Prove.Compile" do
  it "compile + prover.step: NRR end-to-end verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    { prover, tag } <- liftEffect $ compile @PrevsSpecNil @Unit @(F StepField) @Unit @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: unit
      , debug: false
      }
      nrrRule

    eResult <- liftEffect $ runExceptT $ prover.step { appInput: unit, prevs: unit }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("prover.step: " <> show e)
      Right compiledProof ->
        verify (un Tag tag).verifier [ compiledProof ] `shouldEqual` true

  it "compile byte-matches produceNoRecursionReturn (deterministic RNG)" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    -- Path A: via compile.
    { prover: pA, tag: tA } <- liftEffect $ compile @PrevsSpecNil @Unit @(F StepField) @Unit @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: unit
      , debug: false
      }
      nrrRule
    eA <- liftEffect $ runExceptT $ pA.step { appInput: unit, prevs: unit }
    compiledProofA <- case eA of
      Left e -> liftEffect $ Exc.throw ("compile path: " <> show e)
      Right p -> pure p

    -- Path B: via produceNoRecursionReturn.
    artifactsB <- produceNoRecursionReturn
      { vestaSrs, lagrangeSrs: pallasSrs, pallasProofCrs: pallasSrs }

    let CompiledProof cpA = compiledProofA
    -- The wrap proof must be byte-identical. We compare the
    -- messages-digest fields as a sanity proxy (cheap, covers the full
    -- statement). A mismatch here means the compile API's prove path
    -- diverged from the producer's reference path.
    cpA.messagesForNextStepProofDigest `shouldEqual` artifactsB.messagesForNextStepProofDigest
    cpA.messagesForNextWrapProofDigest `shouldEqual` artifactsB.messagesForNextWrapProofDigest
    cpA.challengePolynomialCommitment `shouldEqual` artifactsB.stepProofSg

    -- Verifier's wrapPublicInput helper reconstructs the kimchi wrap
    -- publicInputs Array purely from CompiledProof fields + verifier
    -- constants (via expandDeferredForVerify + wrapPublicInputOf). If
    -- this reconstruction is byte-exact with what wrapSolveAndProve
    -- actually received, InductivePrev can use this helper directly
    -- instead of augmenting CompiledProof with a stored Array.
    wrapPublicInput (un Tag tA).verifier compiledProofA `shouldEqual` artifactsB.wrapPublicInput

  it "compile + prover.step: Simple_chain b0 end-to-end verify returns true" \_ -> do
    let pallasSrs = PallasImpl.pallasCrsCreate (1 `Int.shl` 15)
    vestaSrs <- liftEffect $ createCRS @StepField

    { prover, tag } <- liftEffect $ compile
      @(PrevsSpecCons 1 (StatementIO (F StepField) Unit) PrevsSpecNil)
      @(F StepField)
      @Unit
      @(F StepField)
      @Effect
      { srs: { vestaSrs, pallasSrs }
      , perSlotImportedVKs: unit
      , debug: false
      }
      (simpleChainRule (F (negate one)))

    -- b0: base case — no real prev proof, supply BasePrev with the
    -- dummy input Simple_chain convention uses (self = -1).
    eResult <- liftEffect $ runExceptT $ prover.step
      { appInput: F zero
      , prevs: Tuple (BasePrev { dummyInput: F (negate one) }) unit
      }
    case eResult of
      Left e -> liftEffect $ Exc.throw ("prover.step: " <> show e)
      Right compiledProof ->
        verify (un Tag tag).verifier [ compiledProof ] `shouldEqual` true
